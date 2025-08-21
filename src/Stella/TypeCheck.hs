{-# LANGUAGE PatternSynonyms #-}

module Stella.TypeCheck where

import Stella.Abs
import Stella.ErrM

import Data.Maybe
import Prelude

-- TODO
-- Порефакторить систему сборки

-- 5. Сделать реализацию BindingPattern
-- 6. для расширения #sum-types: TypeSum, Inl, Inr, Match, AMatchCase, PatternInl, PatternInr, PatternVar
-- 7. Пройтись еще раз по охвату ошибок
-- 8. Организовать тестовое покрытие(переназвать файлы, пройтись по кейсам)

data MissingMatchCase
    = MissingInr
    | MissingInl
  deriving (Eq, Ord, Show, Read)

-- Типы ошибок
data CErrType
    = C_ERROR_EXPR_NOT_IMPLEMENTED_YET Expr Type
    | C_ERROR_EXPR_NOT_IMPLEMENTED_YET_I Pattern Pattern Expr Type
    | I_ERROR_EXPR_NOT_IMPLEMENTED_YET Expr
    | C_ERROR_DECL_NOT_IMPLEMENTED_YET Decl
    | ERROR_Unknown_ident_for_binding
    | ERROR_MISSING_MAIN
    | ERROR_UNDEFINED_VARIABLE StellaIdent
    | ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_SILENT
    | ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION Expr Type Type -- Expr Expected Got
    | ERROR_NOT_A_FUNCTION Expr
    | ERROR_NOT_A_TUPLE Expr
    | ERROR_NOT_A_RECORD Expr
    | ERROR_UNEXPECTED_TUPLE_LENGTH Expr Integer
    | ERROR_TUPLE_INDEX_OUT_OF_BOUNDS Expr Integer
    | ERROR_UNEXPECTED_FIELD_ACCESS Expr StellaIdent
    | ERROR_UNEXPECTED_TYPE_FOR_PARAMETER StellaIdent Type Type -- Ident Expected Got
    | ERROR_UNEXPECTED_LAMBDA Expr Type
    | ERROR_AMBIGUOUS_SUM_TYPE Expr
    | ERROR_UNEXPECTED_INJECTION Expr
    | ERROR_NONEXHAUSTIVE_MATCH_PATTERNS Expr MissingMatchCase
    | ERROR_UNEXPECTED_PATTERN_FOR_TYPE Expr [MatchCase]
  deriving (Eq, Ord, Show, Read)

-- Окружение: имя переменной → её тип
type Env = [(StellaIdent, Type)]

updateEnvByParams :: Env -> [ParamDecl] -> Env
updateEnvByParams env params =
    env ++ [(ident, t) | AParamDecl ident t <- params]

-- Результат проверки против типа
type CheckResult = Either CErrType ()

pattern CheckOk :: CheckResult
pattern CheckOk = Right ()

pattern CheckErr :: CErrType -> CheckResult
pattern CheckErr e = Left e

-- Композиция проверок
(>>>) :: CheckResult -> CheckResult -> CheckResult
CheckOk      >>> r = r
CheckErr err >>> _ = CheckErr err

declCheck :: Env -> Decl -> (CheckResult, Env)
declCheck env (DeclFun _ name [] NoReturnType _ _ expr) =
    (exprCheck env expr TypeUnit, env)
declCheck env (DeclFun _ name [] (SomeReturnType retTy) _ _ expr) =
    (exprCheck env expr retTy, env)

declCheck env (DeclFun anns name paramsAnn NoReturnType throwTy decls expr) =
        let (checkRes, initEnv) = declCheck (updateEnvByParams env paramsAnn) (DeclFun anns name [] NoReturnType throwTy decls expr)
    in
        (checkRes, initEnv ++ [(name, TypeFun [t | AParamDecl _ t <- paramsAnn] TypeUnit)])

declCheck env (DeclFun anns name paramsAnn (SomeReturnType retTy) throwTy decls expr) =
        let (checkRes, initEnv) = declCheck (updateEnvByParams env paramsAnn) (DeclFun anns name [] (SomeReturnType retTy) throwTy decls expr)
    in
        (checkRes, initEnv ++ [(name, TypeFun [t | AParamDecl _ t <- paramsAnn] retTy)])

declCheck e d = (CheckErr (C_ERROR_DECL_NOT_IMPLEMENTED_YET d), e)

exprCheck :: Env -> Expr -> Type -> CheckResult

-- ====== T-True ======
exprCheck _ ConstTrue TypeBool =
    CheckOk
exprCheck _ ConstTrue t =
    CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION ConstTrue TypeBool t)

-- ====== T-False ======
exprCheck _ ConstFalse TypeBool =
    CheckOk
exprCheck _ ConstFalse t =
    CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION ConstFalse TypeBool t)

-- ====== T-If ======
exprCheck env (If e1 e2 e3) t = do
    exprCheck env e1 TypeBool
    >>> exprCheck env e2 t
    >>> exprCheck env e3 t

-- ====== T-Zero ======
exprCheck _ (ConstInt 0) TypeNat =
    CheckOk
exprCheck _ (ConstInt 0) t =
    CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (ConstInt 0) TypeNat t)

-- ====== T-Succ ======
exprCheck env (Succ e) TypeNat =
    exprCheck env e TypeNat
exprCheck env (Succ e) t =
    CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (Succ e) TypeNat t)

-- ====== T-Pred ======
exprCheck env (Pred e) TypeNat =
    exprCheck env e TypeNat
exprCheck env (Pred e) t =
    CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (Pred e) TypeNat t)

-- ====== T-IsZero ======
exprCheck env (IsZero e) TypeBool =
    exprCheck env e TypeNat
exprCheck env (IsZero e) t =
    CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (IsZero e) TypeBool t)

-- ====== T-Var ======
exprCheck env (Var ident) t =
    case lookup ident env of
        Just ty ->
            if (ty == t)
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (Var ident) t ty)
        Nothing -> CheckErr (ERROR_UNDEFINED_VARIABLE ident)

-- ====== T-Abs ======
-- 2. Check e with retTy after params
exprCheck env (Abstraction [] e) (TypeFun [] retTy) =
    exprCheck env e retTy

-- Check for length match of params and their types(ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION)
exprCheck env (Abstraction _ e) (TypeFun [] retTy) =
    CheckErr ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_SILENT

-- Check for length match of params and their types(ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION)
exprCheck env (Abstraction [] e) (TypeFun _ retTy) =
    CheckErr ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_SILENT

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
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e1 expectedRetTy actualRetTy)
        InferOk actualTy ->
            CheckErr (ERROR_NOT_A_FUNCTION e1)
        InferErr err ->
            CheckErr err

-- ====== T-Unit ======
exprCheck _ ConstUnit TypeUnit = CheckOk

-- ====== T-Seq ======
exprCheck env (Sequence e1 e2) t =
    exprCheck env e1 TypeUnit
    >>> exprCheck env e2 t

-- ====== T-Ascribe ======
exprCheck env (TypeAsc e ty) t =
    exprCheck env e t

-- ====== T-Let ======
exprCheck env (Let bindings e) t =
    let patternToExpr = [(ptrn, expr) | APatternBinding ptrn expr <- bindings]
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
    CheckErr ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_SILENT

exprCheck env (Tuple []) (TypeTuple _) =
    CheckErr ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_SILENT

exprCheck env (Tuple (e : es)) (TypeTuple (ty : tys)) =
    exprCheck env e ty
    >>> exprCheck env (Tuple es) (TypeTuple tys)

-- ====== T-Proj ======
exprCheck env (DotTuple expr idx) ty =
    case exprInfer env (DotTuple expr idx) of
        InferOk actualTy ->
            if (ty == actualTy)
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (DotTuple expr idx) ty actualTy)
        InferErr err ->
            CheckErr err

-- ====== T-Record ======
exprCheck env (Record []) (TypeRecord []) =
    CheckOk

exprCheck env (Record _) (TypeRecord []) =
    CheckErr ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_SILENT

exprCheck env (Record []) (TypeRecord _) =
    CheckErr ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_SILENT

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
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (DotRecord expr ident) ty actualTy)
        InferErr err ->
            CheckErr err

-- ====== T-Inl ======
exprCheck env (Inl expr) (TypeSum t1 t2) = exprCheck env expr t1

exprCheck env (Inl expr) _ = CheckErr (ERROR_UNEXPECTED_INJECTION expr)

-- ====== T-Inr ======
exprCheck env (Inr expr) (TypeSum t1 t2) = exprCheck env expr t2

exprCheck env (Inr expr) _ = CheckErr (ERROR_UNEXPECTED_INJECTION expr)

-- ====== T-Case ======
-- TODO check match in match
exprCheck env (Match expr cases@[(AMatchCase (PatternInl p1) v1), (AMatchCase (PatternInr p2) v2)]) ty =
    case exprInfer env expr of
        InferOk (TypeSum t1 t2) -> 
            exprCheck (env ++ [(fetchIdent p1, t1)]) v1 ty
            >>> exprCheck (env ++ [(fetchIdent p2, t2)]) v2 ty
        InferOk _ -> CheckErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE expr cases)
        InferErr err -> CheckErr err
exprCheck env (Match expr [(AMatchCase (PatternInl p1) v1), (AMatchCase _ v2)]) ty = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS expr MissingInr)
exprCheck env (Match expr [(AMatchCase _ v1), (AMatchCase (PatternInr p2) v2)]) ty = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS expr MissingInl)

-- TODO сделать реализацию для variant
-- Подумать на тему как разбирать паттерны, надо де откуда-то для patterns stella-ident получать, скорее всего тут и появляется match логика
-- exprCheck env (Match expr [p1, p2]) ty = CheckOk
-- exprCheck env (Match expr matchCases) ty = CheckOk

exprCheck _ e t = CheckErr (C_ERROR_EXPR_NOT_IMPLEMENTED_YET e t)

-- Результат вывода типа
type InferResult = Either CErrType

pattern InferOk :: a -> InferResult a
pattern InferOk x = Right x

pattern InferErr :: CErrType -> InferResult a
pattern InferErr e = Left e

exprInfer :: Env -> Expr -> InferResult Type

-- ====== T-True ======
exprInfer _ ConstTrue  = InferOk TypeBool

-- ====== T-False ======
exprInfer _ ConstFalse = InferOk TypeBool

-- ====== T-If ======
exprInfer env (If e1 e2 e3) = do
    t1 <- exprInfer env e1
    case t1 of
        TypeBool -> do
            ty2 <- exprInfer env e2
            ty3 <- exprInfer env e3
            if ty2 == ty3
                then return ty2
                else InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e3 ty2 ty3)
        ty -> InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e1 TypeBool ty)

-- ====== T-Zero ======
exprInfer _ (ConstInt 0) = InferOk TypeNat

-- ====== T-Succ ======
exprInfer env (Succ e) =
    case exprInfer env e of
        InferOk TypeNat -> 
            InferOk TypeNat
        InferOk ty -> 
            InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e TypeNat ty)
        InferErr err -> 
            InferErr err

-- ====== T-Pred ======
exprInfer env (Pred e) =
    case exprInfer env e of
        InferOk TypeNat ->
            InferOk TypeNat
        InferOk ty ->
            InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e TypeNat ty)
        InferErr err ->
            InferErr err

-- ====== T-IsZero ======
exprInfer env (IsZero e) =
    case exprInfer env e of
        InferOk TypeNat ->
            InferOk TypeBool
        InferOk ty ->
            InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e TypeNat ty)
        InferErr err ->
            InferErr err

-- ====== T-NatRec ======
exprInfer env (NatRec e1 e2 e3) =
    case (exprCheck env e1 TypeNat) of
        CheckErr err -> 
            InferErr err
        CheckOk ->
            case (exprInfer env e2) of
                InferErr err ->
                    InferErr err
                InferOk ty ->
                    case (exprCheck env e3 (TypeFun [TypeNat] (TypeFun [ty] ty))) of
                        CheckErr err ->
                            InferErr err
                        CheckOk ->
                            InferOk ty

-- ====== T-Var ======
exprInfer env (Var ident) =
    case lookup ident env of
        Just t  -> InferOk t
        Nothing -> InferErr (ERROR_UNDEFINED_VARIABLE ident)

-- ====== T-Abs ======
exprInfer env (Abstraction params e) =
    case exprInfer (updateEnvByParams env params) e of
        InferOk ty -> InferOk (TypeFun [t | AParamDecl _ t <- params] ty)
        InferErr err -> InferErr err

-- ====== T-App ======
exprInfer env (Application e1 e2list) = do
    case exprInfer env e1 of
        InferOk (TypeFun paramTys retTy) ->
            if length e2list /= length paramTys
                then InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_SILENT) -- Not matched args length with type
                else case foldl (checkArg env) CheckOk (zip e2list paramTys) of
                    CheckOk ->
                        InferOk retTy
                    CheckErr err ->
                        InferErr err
        InferOk _ ->
            InferErr (ERROR_NOT_A_FUNCTION e1)
        InferErr err ->
            InferErr err
    where
        checkArg :: Env -> CheckResult -> (Expr, Type) -> CheckResult
        checkArg env acc (e, ty) = acc >>> exprCheck env e ty

-- ====== T-Unit ======
exprInfer _ ConstUnit  = InferOk TypeUnit

-- ====== T-Seq ======
exprInfer env (Sequence e1 e2) =
    case exprCheck env e1 TypeUnit of
        CheckOk ->
            exprInfer env e2
        CheckErr err ->
            InferErr err

-- ====== T-Ascribe ======
exprInfer env (TypeAsc e ty) =
    case exprCheck env e ty of
        CheckOk ->
            InferOk ty
        CheckErr err ->
            InferErr err

-- ====== T-Let ======
exprInfer env (Let bindings e) =
    case updateEnvByBindings env bindings of
        Ok env ->
            exprInfer env e
        Bad err ->
            InferErr err

-- ====== T-Tuple ======
exprInfer env (Tuple exprs) =
    foldl step (InferOk (TypeTuple [])) exprs
  where
    step :: InferResult Type -> Expr -> InferResult Type
    step (InferErr err) _ = InferErr err
    step (InferOk (TypeTuple acc)) e =
        case exprInfer env e of
            InferOk ty   -> InferOk (TypeTuple (acc ++ [ty]))
            InferErr err -> InferErr err

-- ====== T-Proj ======
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

-- ====== T-Record ======
exprInfer env (Record bindings) =
        foldl step (InferOk (TypeRecord [])) bindings
    where
        step :: InferResult Type -> Binding -> InferResult Type
        step (InferOk (TypeRecord acc)) (ABinding ident e) =
            case exprInfer env e of
                InferOk ty ->
                    InferOk (TypeRecord (acc ++ [(ARecordFieldType ident ty)]))
                InferErr err ->
                    InferErr err

-- ====== T-RecordProj ======
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

-- ====== T-Inl ======
exprInfer env (Inl expr) = InferErr (ERROR_AMBIGUOUS_SUM_TYPE expr)

-- ====== T-Inr ======
exprInfer env (Inr expr) = InferErr (ERROR_AMBIGUOUS_SUM_TYPE expr)

-- ====== T-Case ======
-- exprInfer env (Match expr matchCases) =
--         let newEnv = foldl step env matchCases
--     in
--         exprInfer newEnv expr
--     where
--         step :: Env -> MatchCase -> Env
--         step e mc =
--             case updateEnvByMatchCase e mc of
--                 Ok ne -> ne
--                 Bad _ -> e

-- Other
exprInfer _ e = InferErr (I_ERROR_EXPR_NOT_IMPLEMENTED_YET e)

indexInteger :: [a] -> Integer -> Maybe a
indexInteger xs n
    | n < 0                         = Nothing
    | n >= fromIntegral (length xs)  = Nothing
    | otherwise                     = Just (xs !! fromIntegral n)

-- -- (-) PatternCastAs Pattern Type
-- -- (-) PatternAsc Pattern Type
-- -- (-) PatternVariant StellaIdent PatternData
-- -- (+) PatternInl Pattern
-- -- (+) PatternInr Pattern
-- -- (-) PatternTuple [Pattern]
-- -- (-) PatternRecord [LabelledPattern]
-- -- (-) PatternList [Pattern]
-- -- (-) PatternCons Pattern Pattern
-- -- (-) PatternFalse
-- -- (-) PatternTrue
-- -- (-) PatternUnit
-- -- (-) PatternInt Integer
-- -- (-) PatternSucc Pattern
-- -- (+) PatternVar StellaIdent
fetchIdent :: Pattern -> Maybe StellaIdent
fetchIdent (PatternVar ident) =
    Just ident
-- fetchIdent (PatternInl p) =
--     fetchIdent p
-- fetchIdent (PatternInr p) =
--     fetchIdent p
fetchIdent _ =
    Nothing

-- TODO дописать заполнение env
-- updateEnvByMatchCase :: Env -> MatchCase -> Either CErrType Env
-- updateEnvByMatchCase env (AMatchCase p e) =
--     case exprInfer env e of
--         InferOk ty ->
--             case fetchIdent p of
--                 Nothing ->
--                     Bad ERROR_Unknown_ident_for_binding
--                 Just ident ->
--                     Ok (env ++ [(ident, ty)])
--         InferErr err ->
--             Bad err

updateEnvByBind :: Env -> PatternBinding -> Either CErrType Env
updateEnvByBind env (APatternBinding p e) =
    case exprInfer env e of
        InferOk ty ->
            case fetchIdent p of
                Just ident ->
                    Ok (env ++ [(ident, ty)])
                Nothing ->
                    Bad (I_ERROR_EXPR_NOT_IMPLEMENTED_YET e)
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