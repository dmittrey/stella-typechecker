module Stella.TypeInfer where

import Stella.TypeCheck

import Stella.Abs
import Stella.ErrM

data InferResult = InferOk Type | InferErr CErrType
  deriving (Show, Eq)

indexInteger :: [a] -> Integer -> Maybe a
indexInteger xs n
    | n < 0                         = Nothing
    | n >= fromIntegral (length xs)  = Nothing
    | otherwise                     = Just (xs !! fromIntegral n)

-- (-) PatternCastAs Pattern Type
-- (-) PatternAsc Pattern Type
-- (-) PatternVariant StellaIdent PatternData
-- (-) PatternInl Pattern
-- (-) PatternInr Pattern
-- (-) PatternTuple [Pattern]
-- (-) PatternRecord [LabelledPattern]
-- (-) PatternList [Pattern]
-- (-) PatternCons Pattern Pattern
-- (-) PatternFalse
-- (-) PatternTrue
-- (-) PatternUnit
-- (-) PatternInt Integer
-- (-) PatternSucc Pattern
-- (+) PatternVar StellaIdent
updateEnvByBind :: Env -> PatternBinding -> Either CErrType Env
updateEnvByBind env (APatternBinding (PatternVar ident) e) =
    case exprInfer env e of
        InferOk ty -> 
            Ok (env ++ [(ident, ty)])
        InferErr err ->
            Bad err

updateEnvByBind env (APatternBinding _ e) = Ok env

updateEnvByBindings :: Env -> [PatternBinding] -> Either CErrType Env
updateEnvByBindings env [] = Ok env
updateEnvByBindings env (x : xs) =
    case updateEnvByBind env x of
        Ok newEnv -> 
            updateEnvByBindings newEnv xs
        Bad err ->
            Bad err

declInfer :: Env -> Decl -> Err (StellaIdent, Type)
-- T-Abs
declInfer env (DeclFun _ name params _ _ _ body) =
    let paramEnv       = [(ident, t) | AParamDecl ident t <- params]
        envWithParams  = paramEnv ++ env
    in case exprInfer envWithParams body of
        InferOk tfunc -> Ok (name, TypeFun [t | AParamDecl _ t <- params] tfunc)
        InferErr err -> Bad $ show err

declInfer _ (DeclFunGeneric _ _ _ _ _ _ _ _) =
    Bad "DeclFunGeneric not supported"
declInfer _ (DeclTypeAlias _ _) =
    Bad "DeclTypeAlias not supported"
declInfer _ (DeclExceptionType _) =
    Bad "DeclExceptionType not supported"
declInfer _ (DeclExceptionVariant _ _) =
    Bad "DeclExceptionVariant not supported"

exprInfer :: Env -> Expr -> InferResult
-- T-Abs
exprInfer env (Abstraction params e) =
    let paramEnv       = [(ident, t) | AParamDecl ident t <- params]
        envWithParams  = paramEnv ++ env
    in case exprInfer envWithParams e of
        InferOk ty -> InferOk (TypeFun [t | AParamDecl _ t <- params] ty)
        InferErr err -> InferErr err

-- T-True
exprInfer _ ConstTrue  = InferOk TypeBool
-- T-False
exprInfer _ ConstFalse = InferOk TypeBool
-- T-If
exprInfer env (If e1 e2 e3) =
    let
        t1 = exprInfer env e1
        t2 = exprInfer env e2
        t3 = exprInfer env e3
    in case t1 of
        InferOk TypeBool ->
            case (t2, t3) of 
                (InferOk ty2, InferOk ty3) ->
                    if ty2 == ty3
                    then InferOk ty2
                    else InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e3 ty2 ty3)
                (InferErr err2, _) ->
                    InferErr err2
                (_, InferErr err3) ->
                    InferErr err3
        InferOk ty ->
            InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e1 TypeBool ty)

        InferErr err -> InferErr err

-- T-Zero
exprInfer _ (ConstInt 0) = InferOk TypeNat
-- T-Succ
exprInfer env (Succ e) = do
    case exprInfer env e of
        InferOk TypeNat -> InferOk TypeNat
        InferOk ty -> InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e TypeNat ty)

        InferErr err -> InferErr err
-- T-Pred
exprInfer env (Pred e) = do
    case exprInfer env e of
        InferOk TypeNat -> InferOk TypeNat
        InferOk ty -> InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e TypeNat ty)

        InferErr err -> InferErr err
-- T-IsZero
exprInfer env (IsZero e) = do
    case exprInfer env e of
        InferOk TypeNat -> InferOk TypeBool
        InferOk ty -> InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e TypeNat ty)

        InferErr err -> InferErr err
-- T-NatRec
exprInfer env (NatRec e1 e2 e3) =
    let
        t1 = exprInfer env e1
        t2 = exprInfer env e2
        t3 = exprInfer env e3
    in case t1 of
        InferOk TypeNat ->
            case t2 of 
                InferOk ty2 ->
                    case t3 of
                        InferOk (TypeFun [TypeNat] (TypeFun [ty21] ty22)) ->
                            if (ty2 == ty21 && ty2 == ty22) --TODO: Migrate to use checkExpr
                            then InferOk ty2
                            else InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e3 (TypeFun [TypeNat] (TypeFun [ty2] ty2)) (TypeFun [TypeNat] (TypeFun [ty21] ty22)))
                        InferErr err -> InferErr err
                InferErr err -> InferErr err
        InferOk ty ->
            InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e1 TypeNat ty)

        InferErr err -> InferErr err

-- T-Var
exprInfer env (Var ident) =
    case lookup ident env of
        Just t  -> InferOk t
        Nothing -> InferErr (ERROR_UNDEFINED_VARIABLE ident)

-- T-App
exprInfer env (Application e1 e2list) =
    case exprInfer env e1 of
        InferOk (TypeFun tys retTy) ->
            case (exprListCheck env e2list tys) of
                CheckOk -> InferOk retTy
                CheckErr err -> InferErr err
        InferOk _ -> InferErr ERROR_NOT_A_FUNCTION

        InferErr err -> InferErr err

-- T-Unit
exprInfer _ ConstUnit  = InferOk TypeUnit

-- T-Seq
-- 
-- t1 ; t2 => T
-- 1. Check t1 <= Unit
-- 2. Infer t2 => T 
exprInfer env (Sequence e1 e2) =
    case exprCheck env e1 TypeUnit of
        CheckOk ->
            exprInfer env e2
        CheckErr err ->
            InferErr err

-- T-Ascribe
-- 
-- t as T => T
-- 1. Check t <= T
-- 2. Return T
exprInfer env (TypeAsc e ty) =
    case exprCheck env e ty of
        CheckOk ->
            InferOk ty
        CheckErr err ->
            InferErr err

-- T-Let
-- 
-- let x = e1 in e2 => T2
-- 1. Infer e1 => T1
-- 2. Add x : T1 to env
-- 3. Infer e2 => T2 with new env
exprInfer env (Let bindings e) =
    case updateEnvByBindings env bindings of
        Ok env ->
            exprInfer env e
        Bad err ->
            InferErr err

-- T-Tuple
-- 
-- {t_1,..,t_n} : {T_1,...,T_n}
-- 1. Infer exprs types
-- 2. Return TypeTuple instance
exprInfer env (Tuple exprs) =
    foldl step (InferOk (TypeTuple [])) exprs
  where
    step :: InferResult -> Expr -> InferResult
    step (InferErr err) _ = InferErr err
    step (InferOk (TypeTuple acc)) e =
        case exprInfer env e of
            InferOk ty   -> InferOk (TypeTuple (acc ++ [ty]))
            InferErr err -> InferErr err

-- T-Proj
-- 
-- t.j => T_j
-- 1. Infer expr type
-- 2. Check if it Tuple type
-- 3. Take idx'th type
exprInfer env (DotTuple expr idx) =
    case exprInfer env expr of
        InferOk (TypeTuple tys) ->
            case indexInteger tys (idx - 1) of
                Just t  -> InferOk t
                Nothing -> InferErr (ERROR_TUPLE_INDEX_OUT_OF_BOUNDS expr idx)
        InferOk otherTy ->
            InferErr (ERROR_NOT_A_TUPLE expr)
        InferErr err ->
            InferErr err

-- Other
exprInfer _ e = InferErr (I_ERROR_EXPR_NOT_IMPLEMENTED_YET e)
