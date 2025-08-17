module Stella.TypeCheck where

import Stella.Abs
import Stella.ErrM

import Data.Maybe
import Prelude

-- TODO
-- Порефакторить систему сборки

-- 6. Пройтись еще раз по охвату ошибок
-- 7. Организовать тестовое покрытие(переназвать файлы, пройтись по кейсам)

-- Окружение: имя переменной → её тип
type Env = [(StellaIdent, Type)]

data CErrType
    = C_ERROR_EXPR_NOT_IMPLEMENTED_YET Expr Type
    | I_ERROR_EXPR_NOT_IMPLEMENTED_YET Expr
    | C_ERROR_DECL_NOT_IMPLEMENTED_YET Decl
    | ERROR_MISSING_MAIN
    | ERROR_UNDEFINED_VARIABLE StellaIdent
    | ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION
    | ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED Expr Type Type -- Expr Expected Got
    | ERROR_NOT_A_FUNCTION Expr
    | ERROR_NOT_A_TUPLE Expr
    | ERROR_NOT_A_RECORD Expr
    | ERROR_UNEXPECTED_TUPLE_LENGTH Expr Integer
    | ERROR_TUPLE_INDEX_OUT_OF_BOUNDS Expr Integer
    | ERROR_UNEXPECTED_FIELD_ACCESS Expr StellaIdent
    | ERROR_UNEXPECTED_TYPE_FOR_PARAMETER StellaIdent Type Type -- Ident Expected Got
    | ERROR_UNEXPECTED_LAMBDA Expr Type
  deriving (Eq, Ord, Show, Read)

data CheckResult = CheckOk | CheckErr CErrType
  deriving (Show, Eq)

(>>>) :: CheckResult -> CheckResult -> CheckResult
CheckOk      >>> r = r
CheckErr err >>> _ = CheckErr err

-- Вспомогательная функция для T-App
exprListCheck :: Env -> [Expr] -> [Type] -> CheckResult
exprListCheck env (e:etail) (ty:tys) =
    case exprCheck env e ty of
        CheckOk ->
            exprListCheck env etail tys
        
        CheckErr err ->
            CheckErr err

exprListCheck _ [] [] = CheckOk

-- T-Abs
declCheck :: Env -> Decl -> Type -> CheckResult
declCheck _ (DeclFun _ name _ retAnn _ _ expr) (TypeFun _ retType) =
    case retAnn of
        NoReturnType ->
            if (retType == TypeUnit)
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED expr TypeUnit retType)

        SomeReturnType annTy ->
            if retType == annTy
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED expr annTy retType)

declCheck _ d _ = CheckErr (C_ERROR_DECL_NOT_IMPLEMENTED_YET d)

exprCheck :: Env -> Expr -> Type -> CheckResult

-- ====== T-True ======
exprCheck _ ConstTrue TypeBool =
    CheckOk
exprCheck _ ConstTrue t = CheckOk
    -- CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED ConstTrue TypeBool t)

-- ====== T-False ======
exprCheck _ ConstFalse TypeBool =
    CheckOk
exprCheck _ ConstFalse t = CheckOk
    -- CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED ConstFalse TypeBool t)

-- ====== T-If ======
exprCheck env (If e1 e2 e3) t = do
    exprCheck env e1 TypeBool
    >>> exprCheck env e2 t
    >>> exprCheck env e3 t

-- ====== T-Zero ======
exprCheck _ (ConstInt 0) TypeNat =
    CheckOk
exprCheck _ (ConstInt 0) t =
    CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED (ConstInt 0) TypeNat t)

-- ====== T-Succ ======
exprCheck env (Succ e) TypeNat =
    exprCheck env e TypeNat
exprCheck env (Succ e) t =
    CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED (Succ e) TypeNat t)

-- ====== T-Pred ======
exprCheck env (Pred e) TypeNat =
    exprCheck env e TypeNat
exprCheck env (Pred e) t =
    CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED (Pred e) TypeNat t)

-- ====== T-IsZero ======
exprCheck env (IsZero e) TypeBool =
    exprCheck env e TypeNat
exprCheck env (IsZero e) t =
    CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED (IsZero e) TypeBool t)

-- ====== T-Var ======
exprCheck env (Var ident) t =
    case lookup ident env of
        Just ty ->
            if (ty == t)
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED (Var ident) t ty)
        Nothing -> CheckErr (ERROR_UNDEFINED_VARIABLE ident)

-- ====== T-Abs ======
-- 2. Check e with retTy after params
exprCheck env (Abstraction [] e) (TypeFun [] retTy) =
    exprCheck env e retTy

-- Check for length match of params and their types(ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION)
exprCheck env (Abstraction _ e) (TypeFun [] retTy) =
    CheckErr ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION

-- Check for length match of params and their types(ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION)
exprCheck env (Abstraction [] e) (TypeFun _ retTy) =
    CheckErr ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION

-- 1. Check param types
exprCheck env (Abstraction ((AParamDecl paramIdent paramGotTy) : params) e) (TypeFun (paramExpectedTy : paramExpectedTys) retTy) =
    if (paramExpectedTy == paramGotTy)
    then exprCheck env (Abstraction params e) (TypeFun paramExpectedTys retTy)
    else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_PARAMETER paramIdent paramExpectedTy paramGotTy)

-- Check type with non TypeFun (ERROR_UNEXPECTED_LAMBDA)
exprCheck env expression@(Abstraction ((AParamDecl paramIdent paramGotTy) : params) e) t =
    CheckErr (ERROR_UNEXPECTED_LAMBDA expression t)

-- ====== T-App ======
exprCheck env (Application e1 e2list) expectedRetTy =
    case exprInfer env e1 of
        InferOk (TypeFun paramsTy actualRetTy) ->
            if (actualRetTy == expectedRetTy)
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED e1 expectedRetTy actualRetTy)
        InferOk actualTy ->
            CheckErr (ERROR_NOT_A_FUNCTION e1)
        InferErr err ->
            CheckErr err

-- ====== T-Seq ======
exprCheck env (Sequence e1 e2) t =
    exprCheck env e1 TypeUnit
    >>> exprCheck env e2 t

-- ====== T-Ascribe ======
exprCheck env (TypeAsc e ty) t =
    exprCheck env e t

-- ====== T-Let ======
exprCheck env (Let bindings e) t =
    let patternToExpr = [(pattern, expr) | APatternBinding pattern expr <- bindings]
        newEnv = foldl step env patternToExpr
    in
        exprCheck newEnv e t
    where
        step :: [(StellaIdent, Type)] -> (Pattern, Expr) -> [(StellaIdent, Type)]
        step env ((PatternVar ident), expr) =
            case exprInfer env expr of
                InferOk ty ->
                    env ++ [(ident, ty)]
                _ ->
                    env
        step env _ = -- TODO
            env

-- ====== T-Tuple ======
exprCheck env (Tuple []) (TypeTuple []) =
    CheckOk

exprCheck env (Tuple _) (TypeTuple []) =
    CheckErr ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION

exprCheck env (Tuple []) (TypeTuple _) =
    CheckErr ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION

exprCheck env (Tuple (e : es)) (TypeTuple (ty : tys)) =
    exprCheck env e ty
    >>> exprCheck env (Tuple es) (TypeTuple tys)

-- ====== T-Proj ======
exprCheck env (DotTuple expr idx) ty =
    case exprInfer env (DotTuple expr idx) of
        InferOk actualTy ->
            if (ty == actualTy)
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED (DotTuple expr idx) ty actualTy)
        InferErr err ->
            CheckErr err

-- ====== T-Record ======
exprCheck env (Record []) (TypeRecord []) =
    CheckOk

exprCheck env (Record _) (TypeRecord []) =
    CheckErr ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION

exprCheck env (Record []) (TypeRecord _) =
    CheckErr ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION

exprCheck env record_e@(Record (ABinding ident e : es)) (TypeRecord (ARecordFieldType l ty : flds)) 
    | ident /= l = CheckErr (ERROR_UNEXPECTED_FIELD_ACCESS record_e ident)   -- порядок/имена не совпали
    | otherwise  =
        exprCheck env e ty
        >>> exprCheck env (Record es) (TypeRecord flds)

-- ====== T-RecordProj ======
-- t.l_j : T_j
exprCheck env (DotRecord expr ident) ty =
    case exprInfer env (DotRecord expr ident) of
        InferOk actualTy ->
            if ty == actualTy
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED (DotRecord expr ident) ty actualTy)
        InferErr err ->
            CheckErr err


exprCheck _ e t = CheckErr (C_ERROR_EXPR_NOT_IMPLEMENTED_YET e t)

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
-- 
-- 1. Update env with params
-- 2. Infer return type
-- 3. Return [param types] -> return type
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
                    else InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED e3 ty2 ty3)
                (InferErr err2, _) ->
                    InferErr err2
                (_, InferErr err3) ->
                    InferErr err3
        InferOk ty ->
            InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED e1 TypeBool ty)

        InferErr err -> InferErr err

-- T-Zero
exprInfer _ (ConstInt 0) = InferOk TypeNat
-- T-Succ
exprInfer env (Succ e) = do
    case exprInfer env e of
        InferOk TypeNat -> InferOk TypeNat
        InferOk ty -> InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED e TypeNat ty)

        InferErr err -> InferErr err
-- T-Pred
exprInfer env (Pred e) = do
    case exprInfer env e of
        InferOk TypeNat -> InferOk TypeNat
        InferOk ty -> InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED e TypeNat ty)

        InferErr err -> InferErr err
-- T-IsZero
exprInfer env (IsZero e) = do
    case exprInfer env e of
        InferOk TypeNat -> InferOk TypeBool
        InferOk ty -> InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED e TypeNat ty)

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
                            else InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED e3 (TypeFun [TypeNat] (TypeFun [ty2] ty2)) (TypeFun [TypeNat] (TypeFun [ty21] ty22)))
                        InferErr err -> InferErr err
                InferErr err -> InferErr err
        InferOk ty ->
            InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_DETAILED e1 TypeNat ty)

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
        InferOk _ -> InferErr (ERROR_NOT_A_FUNCTION e1)

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

-- T-Record
-- 
-- {l_1 = t_1,..,l_n = t_n} : {l_1 : T_1,...,l_n : T_n}
-- 1. Infer exprs types
-- 2. Return TypeRecord instance
exprInfer env (Record bindings) =
        foldl step (InferOk (TypeRecord [])) bindings
    where
        step :: InferResult -> Binding -> InferResult
        step (InferOk (TypeRecord acc)) (ABinding ident e) =
            case exprInfer env e of
                InferOk ty ->
                    InferOk (TypeRecord (acc ++ [(ARecordFieldType ident ty)]))
                InferErr err ->
                    InferErr err

-- T-RecordProj
-- 
-- t.l_j => T_j
-- 1. Infer t type
-- 2. Get l_j from inferred type
exprInfer env (DotRecord expr ident) =
    case exprInfer env expr of
        InferOk (TypeRecord fields) ->
            let identToType = [(ident, t) | ARecordFieldType ident t <- fields]
            in case lookup ident identToType of
                Just ty  -> InferOk ty
                Nothing -> InferErr (ERROR_UNEXPECTED_FIELD_ACCESS expr ident)
        InferOk otherTy ->
            InferErr (ERROR_NOT_A_RECORD expr)
        InferErr err ->
            InferErr err 

-- Other
exprInfer _ e = InferErr (I_ERROR_EXPR_NOT_IMPLEMENTED_YET e)
