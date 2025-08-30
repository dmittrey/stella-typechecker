{-# LANGUAGE PatternSynonyms #-}

module Stella.TypeCheck where

import Stella.Abs
import Stella.ErrM

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Maybe
import Data.List
import Prelude

data MissingMatchCase
    = MissingInr
    | MissingInl
  deriving (Eq, Ord, Show, Read)

-- #structural-patterns 
-- CI

-- Типы ошибок
data CErrType
    = ERROR_DECL_CHECK_NOT_IMPLEMENTED Decl
    | ERROR_EXPR_CHECK_NOT_IMPLEMENTED Expr Type
    | ERROR_EXPR_INFER_NOT_IMPLEMENTED Expr
    | ERROR_PATTERN_NOT_SUPPORTED Pattern Type
    | ERROR_MATCH_NOT_SUPPORTED Type
    | ERROR_PATTERN_TYPE_REQUIRED_FOR_LETREC Pattern

    | ERROR_MISSING_MAIN
    | ERROR_UNDEFINED_VARIABLE StellaIdent
    | ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_S
    | ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION Expr Type Type -- Expr Expected Got
    | ERROR_NOT_A_FUNCTION Expr
    | ERROR_NOT_A_TUPLE Expr
    | ERROR_NOT_A_RECORD Expr
    | ERROR_UNEXPECTED_LAMBDA Expr Type
    | ERROR_UNEXPECTED_TYPE_FOR_PARAMETER StellaIdent Type Type -- Ident Expected Got
    | ERROR_UNEXPECTED_TUPLE Expr Type
    | ERROR_UNEXPECTED_RECORD Expr Type
    | ERROR_UNEXPECTED_VARIANT Expr
    | ERROR_UNEXPECTED_LIST Expr
    | ERROR_UNEXPECTED_INJECTION Expr
    | ERROR_MISSING_RECORD_FIELDS
    | ERROR_UNEXPECTED_RECORD_FIELDS
    | ERROR_UNEXPECTED_FIELD_ACCESS Expr StellaIdent
    | ERROR_UNEXPECTED_VARIANT_LABEL StellaIdent
    | ERROR_TUPLE_INDEX_OUT_OF_BOUNDS Expr Integer
    | ERROR_UNEXPECTED_TUPLE_LENGTH
    | ERROR_AMBIGUOUS_SUM_TYPE Expr
    | ERROR_AMBIGUOUS_VARIANT_TYPE Expr
    | ERROR_AMBIGUOUS_LIST
    | ERROR_NOT_A_LIST Type
    | ERROR_ILLEGAL_EMPTY_MATCHING
    | ERROR_NONEXHAUSTIVE_MATCH_PATTERNS [MatchCase]
    | ERROR_UNEXPECTED_PATTERN_FOR_TYPE Type
    | ERROR_UNEXPECTED_PATTERN_FOR_TYPE_M Pattern Type
    | ERROR_DUPLICATE_RECORD_FIELDS
    | ERROR_DUPLICATE_RECORD_TYPE_FIELDS
    | ERROR_DUPLICATE_VARIANT_TYPE_FIELDS Type
    | ERROR_INCORRECT_ARITY_OF_MAIN
    | ERROR_INCORRECT_NUMBER_OF_ARGUMENTS
    | ERROR_UNEXPECTED_NUMBER_OF_PARAMETERS_IN_LAMBDA
    | ERROR_UNEXPECTED_DATA_FOR_NULLARY_LABEL
    | ERROR_MISSING_DATA_FOR_LABEL
    | ERROR_UNEXPECTED_NON_NULLARY_VARIANT_PATTERN
    | ERROR_UNEXPECTED_NULLARY_VARIANT_PATTERN
  deriving (Eq, Ord, Show, Read)

-- Окружение: имя переменной → её тип
type Env = [(StellaIdent, Type)]

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

updateEnvByParams :: Env -> [ParamDecl] -> Env
updateEnvByParams env params =
    env ++ [(ident, t) | AParamDecl ident t <- params]

checkArgs :: Env -> [Expr] -> [Type] -> CheckResult
checkArgs _   []     []     = CheckOk
checkArgs _   []     _      = CheckErr ERROR_INCORRECT_NUMBER_OF_ARGUMENTS
checkArgs _   _      []     = CheckErr ERROR_INCORRECT_NUMBER_OF_ARGUMENTS
checkArgs env (e:es) (ty:tys) =
  exprCheck env e ty
  >>> checkArgs env es tys

declCheck :: Env -> Decl -> (CheckResult, Env)
declCheck env (DeclFun _ name [] NoReturnType _ _ expr) =
    (exprCheck env expr TypeUnit, env)
declCheck env (DeclFun _ name [] (SomeReturnType retTy) _ _ expr) =
    (exprCheck env expr retTy, env)

-- Core, #nested-function-declarations, #nullary-functions
declCheck env (DeclFun anns funIdent@(StellaIdent funName) paramsAnn retTy throwTy decls expr) =
    let
        resultTy = case retTy of
                    NoReturnType      -> TypeUnit
                    SomeReturnType ty -> ty

        funTy    = TypeFun [t | AParamDecl _ t <- paramsAnn] resultTy

        -- Функция должна быть доступна самой себе (для рекурсии)
        envWithFun = env ++ [(funIdent, funTy)]

        -- добавляем параметры в локальное окружение
        env' = updateEnvByParams envWithFun paramsAnn

        -- сначала обрабатываем внутренние функции/decls
        (resInner, envInner) = foldl step (CheckOk, env') decls

        -- проверка тела
        resBody = exprCheck envInner expr resultTy

        isMainUnary =
          if funName == "main"
            then if length paramsAnn /= 1
                   then CheckErr ERROR_INCORRECT_ARITY_OF_MAIN
                   else CheckOk
            else CheckOk
    in
        (isMainUnary >>> resBody >>> resInner, envWithFun)
  where
    step (CheckOk, envAcc) d = declCheck envAcc d
    step (CheckErr err, envAcc) _ = (CheckErr err, envAcc)

declCheck e d = (CheckErr (ERROR_DECL_CHECK_NOT_IMPLEMENTED d), e)

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

-- ====== T-NatRec ======
exprCheck env (NatRec n z s) ty =
    exprCheck env n TypeNat
    >>> exprCheck env z ty
    >>> exprCheck env s (TypeFun [TypeNat] (TypeFun [ty] ty))

-- ====== T-Var ======
exprCheck env (Var ident) t =
  case lookup ident env of
    Just ty | ty == t   -> CheckOk
            | otherwise -> CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (Var ident) ty t)
    Nothing             -> CheckErr (ERROR_UNDEFINED_VARIABLE ident)

-- ====== T-Abs ======
exprCheck env (Abstraction params e) (TypeFun expParamTys retTy) =
    case checkParams env params expParamTys of
        (CheckOk, newEnv) -> exprCheck newEnv e retTy
        (CheckErr err, _) -> CheckErr err
  where
    checkParams :: Env -> [ParamDecl] -> [Type] -> (CheckResult, Env)
    checkParams env [] [] = (CheckOk, env)
    checkParams env ((AParamDecl ident actualTy):ps) (ty:tys)
        | length ps /= length tys = (CheckErr ERROR_UNEXPECTED_NUMBER_OF_PARAMETERS_IN_LAMBDA, env)
        | actualTy /= ty = (CheckErr (ERROR_UNEXPECTED_TYPE_FOR_PARAMETER ident ty actualTy), env)
        | otherwise =
            let (res, env') = checkParams env ps tys
            in (res, env' ++ [(ident, actualTy)])

-- Check type with non TypeFun (ERROR_UNEXPECTED_LAMBDA)
exprCheck env expression@(Abstraction ((AParamDecl paramIdent paramGotTy) : params) e) t =
    CheckErr (ERROR_UNEXPECTED_LAMBDA expression t)

-- ====== T-App ======
exprCheck env (Application t1 args) expectedTy =
  case exprInfer env t1 of
    InferOk (TypeFun paramTys resultTy)
      | resultTy == expectedTy ->
          checkArgs env args paramTys
      | otherwise ->
          CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION
                      t1
                      (TypeFun paramTys expectedTy)
                      (TypeFun paramTys resultTy))
    InferOk _ ->
      CheckErr (ERROR_NOT_A_FUNCTION t1)
    InferErr err ->
      CheckErr err

-- ====== T-Unit ======
exprCheck _ ConstUnit TypeUnit = CheckOk
exprCheck _ ConstUnit t =
    CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (ConstUnit) TypeUnit t)

-- ====== T-Seq ======
exprCheck env (Sequence e1 e2) t =
    exprCheck env e1 TypeUnit
    >>> exprCheck env e2 t

-- ====== T-Ascribe ======
exprCheck env (TypeAsc e ty) t =
    exprCheck env e t

-- ====== T-Let ======
exprCheck env (Let bindings expr) t =
    case foldl step (InferOk env) bindings of
        InferOk env' -> 
            exprCheck env' expr t
        InferErr err ->
            CheckErr err
  where
    step :: InferResult Env -> PatternBinding -> InferResult Env
    step (InferOk env) (APatternBinding p e) =
        case exprInfer env e of
            InferOk ty ->
                bindPattern env p ty
            InferErr err ->
                InferErr err

-- ====== T-LetRec ======
exprCheck env (LetRec bindings body) tyC =
    case foldl step (InferOk env) bindings of
        InferOk env' -> exprCheck env' body tyC
        InferErr err -> CheckErr err
  where
    step :: InferResult Env -> PatternBinding -> InferResult Env
    step (InferOk envAcc) (APatternBinding pat e) =
        case pat of
            PatternAsc p@(PatternVar pIdent) tyAnn ->
                case bindPattern (envAcc ++ [(pIdent, tyAnn)]) p tyAnn of
                    InferOk env' -> 
                        case exprCheck env' e tyAnn of
                            CheckOk -> InferOk env'
                            CheckErr err -> InferErr err
                    InferErr err -> InferErr err
            _ -> InferErr (ERROR_PATTERN_TYPE_REQUIRED_FOR_LETREC pat)

    step (InferErr err) _ = InferErr err

-- ====== T-Tuple ======
exprCheck env (Tuple []) (TypeTuple []) =
    CheckOk

exprCheck env (Tuple _) (TypeTuple []) =
    CheckErr ERROR_UNEXPECTED_TUPLE_LENGTH

exprCheck env (Tuple []) (TypeTuple _) =
    CheckErr ERROR_UNEXPECTED_TUPLE_LENGTH

exprCheck env (Tuple (e : es)) (TypeTuple (ty : tys)) =
    exprCheck env e ty
    >>> exprCheck env (Tuple es) (TypeTuple tys)

exprCheck env expression@(Tuple _) ty =
    CheckErr (ERROR_UNEXPECTED_TUPLE expression ty)

-- ====== T-DotTuple ======
exprCheck env expression@(DotTuple expr idx) ty =
    case exprInfer env expr of
        InferOk (TypeTuple tys)
            | idx <= 0                              -> CheckErr (ERROR_TUPLE_INDEX_OUT_OF_BOUNDS expr idx)
            | (fromIntegral idx) > (length tys)     -> CheckErr (ERROR_TUPLE_INDEX_OUT_OF_BOUNDS expr idx)
            | (tys !! (fromIntegral idx - 1)) == ty -> CheckOk
            | otherwise                             -> CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION expression ty (tys !! (fromIntegral idx))) 
        InferOk _                                   -> CheckErr (ERROR_NOT_A_TUPLE expr)
        InferErr err                                -> CheckErr err

-- ====== T-Record ======
exprCheck env (Record []) (TypeRecord []) =
    CheckOk

exprCheck env (Record bindings) (TypeRecord fields) =
    let origBindingsLen = length bindings
        origFieldsLen   = length fields
        bindingsMap     = Map.fromList [(name, val) | ABinding name val <- bindings]
        fieldsMap       = Map.fromList [(name, ty)  | ARecordFieldType name ty <- fields]
        bindingNames    = Map.keysSet bindingsMap
        fieldNames      = Map.keysSet fieldsMap

        checkFields :: [(StellaIdent, Type)] -> CheckResult
        checkFields [] = CheckOk
        checkFields ((name, ty) : rest) =
            case Map.lookup name bindingsMap of
                Just val -> exprCheck env val ty >>> checkFields rest
                Nothing  -> CheckErr ERROR_MISSING_RECORD_FIELDS
    in if Map.size fieldsMap /= origFieldsLen
        then CheckErr ERROR_DUPLICATE_RECORD_TYPE_FIELDS
       else if Map.size bindingsMap /= origBindingsLen
        then CheckErr ERROR_DUPLICATE_RECORD_FIELDS
       else if not (Set.isSubsetOf fieldNames bindingNames)
        then CheckErr ERROR_MISSING_RECORD_FIELDS
       else if not (Set.isSubsetOf bindingNames fieldNames)
        then CheckErr ERROR_UNEXPECTED_RECORD_FIELDS
       else checkFields (Map.toList fieldsMap)

exprCheck env expression@(Record _) ty =
    CheckErr (ERROR_UNEXPECTED_RECORD expression ty)

-- ====== T-DotRecord ======
exprCheck env (DotRecord expr ident) ty =
    case exprInfer env expr of
        InferOk (TypeRecord fields) ->
            let identToType = [(i, ty)  | ARecordFieldType i ty <- fields]
            in
                case lookup ident identToType of
                    Just actualTy
                        | actualTy /= ty    -> CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION expr ty actualTy)
                        | otherwise         -> CheckOk
                    Nothing                 -> CheckErr (ERROR_UNEXPECTED_FIELD_ACCESS expr ident)
        InferOk _                           -> CheckErr (ERROR_NOT_A_RECORD expr)
        InferErr err                        -> CheckErr err

-- ====== T-Inl ======
exprCheck env (Inl expr) (TypeSum t1 t2) = exprCheck env expr t1

exprCheck env (Inl expr) _ = CheckErr (ERROR_UNEXPECTED_INJECTION expr)

-- -- ====== T-Inr ======
exprCheck env (Inr expr) (TypeSum t1 t2) = exprCheck env expr t2

exprCheck env (Inr expr) _ = CheckErr (ERROR_UNEXPECTED_INJECTION expr)

-- ====== T-Variant ======
exprCheck env (Variant ident exprData) (TypeVariant fields) =
    -- Проверяем на дубликаты в типе варианта
    let fieldNames = [ name | AVariantFieldType name _ <- fields ]
    in  if length fieldNames /= Set.size (Set.fromList fieldNames)
            then CheckErr (ERROR_DUPLICATE_VARIANT_TYPE_FIELDS (TypeVariant fields))
        else
            case lookupVariantField ident fields of
                VariantFieldExistSomeType ty ->
                    case exprData of
                        NoExprData -> CheckErr (ERROR_MISSING_DATA_FOR_LABEL)
                        SomeExprData expr -> exprCheck env expr ty
                VariantFieldExistNoType ->
                    case exprData of
                        NoExprData -> CheckOk
                        SomeExprData expr -> CheckErr (ERROR_UNEXPECTED_DATA_FOR_NULLARY_LABEL)
                VariantFieldMissing -> CheckErr (ERROR_UNEXPECTED_VARIANT_LABEL ident)

exprCheck _ expr@(Variant _ _) _ = CheckErr (ERROR_UNEXPECTED_VARIANT expr)

-- ====== T-Head ======
exprCheck env (Head expr) ty =
    exprCheck env expr (TypeList ty)

-- ====== T-Tail ======
exprCheck env (Tail expr) ty =
    exprCheck env expr (TypeList ty)

-- ====== T-IsEmpty ======
exprCheck env (IsEmpty expr) TypeBool =
    case exprInfer env expr of
        InferErr err ->
            CheckErr err
        InferOk (TypeList ty) ->
            CheckOk
        InferOk ty ->
            CheckErr (ERROR_NOT_A_LIST ty)

exprCheck env e@(IsEmpty expr) ty =
    CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e TypeBool ty)

-- ====== T-List ======
exprCheck env (List []) (TypeList ty) = 
    CheckOk

exprCheck env (List (e : [])) (TypeList ty) =
    exprCheck env e ty

exprCheck env (List (e : exprs)) (TypeList ty) =
    exprCheck env e ty
    >>> exprCheck env (List exprs) (TypeList ty)

exprCheck env e@(List exprs) ty =
    CheckErr (ERROR_UNEXPECTED_LIST e)

-- ====== T-ConsList ======
exprCheck env (ConsList e1 e2) (TypeList ty) =
    exprCheck env e1 ty
    >>> exprCheck env e2 (TypeList ty)

exprCheck env e@(ConsList e1 e2) ty =
    CheckErr (ERROR_UNEXPECTED_LIST e)

-- ====== T-Fix ======
exprCheck env (Fix expr@(Abstraction params e)) ty =
    exprCheck env expr (TypeFun [ty] ty)

exprCheck env (Fix expr@(Var ident)) ty =
    exprCheck env expr (TypeFun [ty] ty)

exprCheck env (Fix expr) ty = CheckErr (ERROR_NOT_A_FUNCTION expr)

-- -- ====== T-Case ======
exprCheck env (Match t []) tyC =
    CheckErr ERROR_ILLEGAL_EMPTY_MATCHING

-- При проверке против типа, я должен вывести тип терма, а потом подставляя match case проверять против типа tyC
exprCheck env (Match t cases) tyC =
    case exprInfer env t of
        InferErr err -> CheckErr err
        InferOk ty  -> checkMatchCases env cases ty tyC

-- ====== T-Natural ======
exprCheck _ (ConstInt n) TypeNat = CheckOk -- #natural-literals
exprCheck _ (ConstInt n) t =
    CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (ConstInt n) TypeNat t)

-- ====== Other ======

-- T-Add
exprCheck env (Add e1 e2) TypeNat = 
    exprCheck env e1 TypeNat
    >>> exprCheck env e2 TypeNat

-- T-Equal
exprCheck env (Equal e1 e2) t =
    case exprInfer env e1 of
        InferOk ty1 ->
            exprCheck env e2 ty1
        InferErr err ->
            CheckErr err

exprCheck _ e t = CheckErr (ERROR_EXPR_CHECK_NOT_IMPLEMENTED e t)

-- -- Результат вывода типа
type InferResult = Either CErrType

pattern InferOk :: a -> InferResult a
pattern InferOk x = Right x

pattern InferErr :: CErrType -> InferResult a
pattern InferErr e = Left e

exprInfer :: Env -> Expr -> InferResult Type

-- -- ====== T-True ======
exprInfer _ ConstTrue  = InferOk TypeBool

-- -- ====== T-False ======
exprInfer _ ConstFalse = InferOk TypeBool

-- -- ====== T-If ======
exprInfer env (If t1 t2 t3) =
    case exprInfer env t1 of
        InferOk TypeBool ->
            case exprInfer env t2 of
                InferOk actualT ->
                    case exprCheck env t3 actualT of
                        CheckOk ->
                            InferOk actualT
                        CheckErr err ->
                            InferErr err
                InferErr err ->
                    InferErr err
        InferOk ty ->
            InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION t1 TypeBool ty)
        InferErr err ->
            InferErr err

-- ====== T-Zero ======
exprInfer _ (ConstInt 0) = InferOk TypeNat

-- -- ====== T-Succ ======
exprInfer env (Succ e) =
    case exprCheck env e TypeNat of
        CheckOk ->
            InferOk TypeNat
        CheckErr err ->
            InferErr err

-- -- ====== T-Pred ======
exprInfer env (Pred e) =
    case exprCheck env e TypeNat of
        CheckOk ->
            InferOk TypeNat
        CheckErr err ->
            InferErr err

-- ====== T-IsZero ======
exprInfer env (IsZero e) =
    case exprCheck env e TypeNat of
        CheckOk ->
            InferOk TypeBool
        CheckErr err ->
            InferErr err

-- ====== T-NatRec ======
exprInfer env (NatRec n z s) =
    case exprCheck env n TypeNat of
        CheckErr err -> 
            InferErr err
        CheckOk ->
            case (exprInfer env z) of
                InferErr err ->
                    InferErr err
                InferOk actualT ->
                    case (exprCheck env s (TypeFun [TypeNat] (TypeFun [actualT] actualT))) of
                        CheckErr err ->
                            InferErr err
                        CheckOk ->
                            InferOk actualT

-- -- ====== T-Var ======
exprInfer env (Var ident) =
    case lookup ident env of
        Just t  -> InferOk t
        Nothing -> InferErr (ERROR_UNDEFINED_VARIABLE ident)

-- -- ====== T-Abs ======
exprInfer env (Abstraction params e) =
    case exprInfer (updateEnvByParams env params) e of
        InferOk ty ->
            InferOk (TypeFun [t | AParamDecl _ t <- params] ty)
        InferErr err ->
            InferErr err

-- ====== T-App ======
exprInfer env (Application t1 args) =
  case exprInfer env t1 of
    InferOk (TypeFun paramTys retTy) ->
      case checkArgs env args paramTys of
        CheckOk      -> InferOk retTy
        CheckErr err -> InferErr err
    InferOk _ ->
      InferErr (ERROR_NOT_A_FUNCTION t1)
    InferErr err ->
      InferErr err

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
exprInfer env (Let bindings expr) =
    case foldl step (InferOk env) bindings of
        InferOk env' -> 
            exprInfer env' expr
        InferErr err ->
            InferErr err
  where
    step :: InferResult Env -> PatternBinding -> InferResult Env
    step (InferOk env) (APatternBinding p e) =
        case exprInfer env e of
            InferOk ty ->
                bindPattern env p ty
            InferErr err ->
                InferErr err

-- -- ====== T-Tuple ======
exprInfer env (Tuple exprs) =
    foldl step (InferOk (TypeTuple [])) exprs
  where
    step :: InferResult Type -> Expr -> InferResult Type
    step (InferErr err) _ = InferErr err
    step (InferOk (TypeTuple acc)) e =
        case exprInfer env e of
            InferOk ty   -> InferOk (TypeTuple (acc ++ [ty]))
            InferErr err -> InferErr err

-- ====== T-DotTuple ======
exprInfer env expression@(DotTuple expr idx) =
    case exprInfer env expr of
        InferOk (TypeTuple tys)
            | idx <= 0                              -> InferErr (ERROR_TUPLE_INDEX_OUT_OF_BOUNDS expr idx)
            | (fromIntegral idx) > (length tys)     -> InferErr (ERROR_TUPLE_INDEX_OUT_OF_BOUNDS expr idx)
            | otherwise                             -> InferOk (tys !! (fromIntegral idx - 1))
        InferOk _                                   -> InferErr (ERROR_NOT_A_TUPLE expr)
        InferErr err                                -> InferErr err

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

-- ====== T-DotRecord ======
exprInfer env (DotRecord expr ident) =
    case exprInfer env expr of
        InferOk (TypeRecord fields) ->
            let identToType = [(ident, t) | ARecordFieldType ident t <- fields]
            in case lookup ident identToType of
                Just ty         -> InferOk ty
                Nothing         -> InferErr (ERROR_UNEXPECTED_FIELD_ACCESS expr ident)
        InferOk otherTy         -> InferErr (ERROR_NOT_A_RECORD expr)
        InferErr err            -> InferErr err

-- ====== T-Inl ======
exprInfer env (Inl expr) = InferErr (ERROR_AMBIGUOUS_SUM_TYPE expr)

-- ====== T-Inr ======
exprInfer env (Inr expr) = InferErr (ERROR_AMBIGUOUS_SUM_TYPE expr)

-- ====== T-Variant ======
exprInfer env expr@(Variant ident exprData) = InferErr (ERROR_AMBIGUOUS_VARIANT_TYPE expr)

-- ====== T-Head ======
exprInfer env (Head expr) =
    case exprInfer env expr of
        InferOk (TypeList ty) ->
            InferOk ty
        InferOk ty ->
            InferErr (ERROR_NOT_A_LIST ty)
        InferErr err ->
            InferErr err

-- ====== T-Tail ======
exprInfer env (Tail expr) =
    case exprInfer env expr of
        InferOk (TypeList ty) ->
            InferOk ty
        InferOk ty ->
            InferErr (ERROR_NOT_A_LIST ty)
        InferErr err ->
            InferErr err

-- ====== T-IsEmpty ======
exprInfer env (IsEmpty expr) =
    case exprInfer env expr of
        InferOk (TypeList ty) ->
            InferOk TypeBool
        InferOk ty ->
            InferErr (ERROR_NOT_A_LIST ty)
        InferErr err ->
            InferErr err

-- ====== T-List ======
exprInfer env (List []) =
    InferErr ERROR_AMBIGUOUS_LIST

exprInfer env (List (e:es)) =
    case exprInfer env e of
        InferErr err -> InferErr err
        InferOk tyElem -> checkAll es tyElem
  where
    checkAll :: [Expr] -> Type -> InferResult Type
    checkAll [] ty = InferOk (TypeList ty)
    checkAll (x:xs) ty =
        case exprCheck env x ty of
            CheckErr err -> InferErr err
            CheckOk      -> checkAll xs ty


-- ====== T-ConsList ======
exprInfer env (ConsList e1 e2) =
    case exprInfer env e1 of
        InferOk ty ->
            case exprCheck env e2 (TypeList ty) of
                CheckOk ->
                    InferOk (TypeList ty)
                CheckErr err ->
                    InferErr err
        InferErr err ->
            InferErr err

-- ====== T-Fix ======
exprInfer env (Fix expr) =
    case exprInfer env expr of
        InferOk (TypeFun paramTys retTy) ->
            case exprCheck env expr (TypeFun [retTy] retTy) of
                CheckOk ->
                    InferOk retTy
                CheckErr err ->
                    InferErr err
        InferOk ty ->
            InferErr (ERROR_NOT_A_FUNCTION expr)
        InferErr err ->
            InferErr err

-- ====== T-Natural ======
exprInfer _ (ConstInt n) = InferOk TypeNat -- #natural-literals

-- Other

exprInfer _ e = InferErr (ERROR_EXPR_INFER_NOT_IMPLEMENTED e)

-- ====== Pattern Matching ======

-- (-) TypeAuto
-- (-) TypeFun [Type] Type
-- (-) TypeForAll [StellaIdent] Type
-- (-) TypeRec StellaIdent Type
-- (+) TypeSum Type Type
-- (+) TypeTuple [Type]
-- (+) TypeRecord [RecordFieldType]
-- (+) TypeVariant [VariantFieldType]
-- (+) TypeList Type
-- (+) TypeBool
-- (+) TypeNat
-- (+) TypeUnit
-- (-) TypeTop
-- (-) TypeBottom
-- (-) TypeRef Type
-- (-) TypeVar StellaIdent
checkMatchCases :: Env -> [MatchCase] -> Type -> Type -> CheckResult

-- TypeAuto
checkMatchCases env cases TypeAuto tyC =
    CheckErr (ERROR_MATCH_NOT_SUPPORTED TypeAuto)

-- TypeFun
checkMatchCases env cases t@(TypeFun paramTys retTy) tyC =
    CheckErr (ERROR_MATCH_NOT_SUPPORTED t)

-- TypeForAll
checkMatchCases env cases t@(TypeForAll idents ty) tyC =
    CheckErr (ERROR_MATCH_NOT_SUPPORTED t)

-- TypeRec
checkMatchCases env cases t@(TypeRec ident ty) tyC =
    CheckErr (ERROR_MATCH_NOT_SUPPORTED t)

-- TypeSum
checkMatchCases env cases (TypeSum t1 t2) tyC =
    checkMatchCasesSum env cases (TypeSum t1 t2) tyC

-- TypeTuple
checkMatchCases env cases (TypeTuple tys) tyC =
    checkMatchCasesTuple env cases (TypeTuple tys) tyC

-- TypeRecord
checkMatchCases env cases (TypeRecord fields) tyC =
    checkMatchCasesRecord env cases (TypeRecord fields) tyC

-- TypeVariant
checkMatchCases env cases (TypeVariant fields) tyC =
    checkMatchCasesVariant env cases (TypeVariant fields) tyC

-- TypeList
checkMatchCases env cases (TypeList ty) tyC =
    checkMatchCasesList env cases (TypeList ty) tyC

-- TypeBool
checkMatchCases env cases TypeBool tyC =
    checkMatchCasesBool env cases tyC

-- TypeNat
checkMatchCases env cases TypeNat tyC =
    checkMatchCasesNat env cases tyC

-- TypeUnit
checkMatchCases env cases TypeUnit tyC =
    checkMatchCasesUnit env cases tyC

-- TypeTop
checkMatchCases env cases TypeTop tyC =
    CheckErr (ERROR_MATCH_NOT_SUPPORTED TypeTop)

-- TypeBottom
checkMatchCases env cases TypeBottom tyC =
    CheckErr (ERROR_MATCH_NOT_SUPPORTED TypeBottom)

-- TypeRef
checkMatchCases env cases t@(TypeRef ty) tyC =
    CheckErr (ERROR_MATCH_NOT_SUPPORTED t)

-- TypeVar
checkMatchCases env cases t@(TypeVar ident) tyC =
    CheckErr (ERROR_MATCH_NOT_SUPPORTED t)


checkMatchCasesSum :: Env -> [MatchCase] -> Type -> Type -> CheckResult
checkMatchCasesSum env cases (TypeSum tl tr) tyC =
    go cases False False
  where
    go [] seenL seenR
      | not seenL = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases)
      | not seenR = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases)
      | otherwise = CheckOk
    go (AMatchCase pat expr : rest) seenL seenR =
        case pat of
          PatternInl pl ->
              let res = bindPattern env pl tl >>= \envL -> exprCheck envL expr tyC
              in res >>> go rest True seenR
          PatternInr pr ->
              let res = bindPattern env pr tr >>= \envR -> exprCheck envR expr tyC
              in res >>> go rest seenL True
          _ -> CheckErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeSum tl tr))

checkMatchCasesTuple :: Env -> [MatchCase] -> Type -> Type -> CheckResult
checkMatchCasesTuple env cases (TypeTuple tys) tyC =
    go cases tys
  where
    go [] _ = CheckOk
    go (AMatchCase pat expr : rest) tys =
        case pat of
            PatternTuple pats ->
                let bindAll e [] [] = InferOk e
                    bindAll e (p:ps) (t:ts) =
                        bindPattern e p t >>= \e' -> bindAll e' ps ts
                    bindAll _ _ _ = InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeTuple tys))
                in case bindAll env pats tys of
                     InferErr err -> CheckErr err
                     InferOk env' -> exprCheck env' expr tyC >>> go rest tys
            _ -> CheckErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeTuple tys))

checkMatchCasesRecord :: Env -> [MatchCase] -> Type -> Type -> CheckResult
checkMatchCasesRecord env cases (TypeRecord fields) tyC =
    go cases fields
  where
    go [] _ = CheckOk
    go (AMatchCase pat expr : rest) fields =
        case pat of
            PatternRecord pats ->
                let identToType = [(i, ty)  | ARecordFieldType i ty <- fields]
                    bindAll e [] = InferOk e
                    bindAll e ((ALabelledPattern ident identPat):ps) =
                        case lookup ident identToType of
                            Just ty ->
                                bindPattern e identPat ty >>= \e' -> bindAll e' ps
                            Nothing -> InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeRecord fields))
                in case bindAll env pats of
                     InferErr err -> CheckErr err
                     InferOk env' -> exprCheck env' expr tyC >>> go rest fields
            _ -> CheckErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeRecord fields))

checkMatchCasesVariant :: Env -> [MatchCase] -> Type -> Type -> CheckResult
checkMatchCasesVariant env cases (TypeVariant fields) tyC =
    let initialMap = Map.fromList [(ident, False) | AVariantFieldType ident ty <- fields]
  in
    go cases initialMap
  where
    go [] seenMap
      | not (all id (Map.elems seenMap)) = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases)
      | otherwise                        = CheckOk
    go (AMatchCase pat expr : rest) seenMap =
        case pat of
            PatternVariant ident patData ->
                case patData of
                    NoPatternData       ->
                        case lookupVariantField ident fields of
                            VariantFieldExistSomeType ty ->
                                CheckErr ERROR_UNEXPECTED_NULLARY_VARIANT_PATTERN
                            VariantFieldExistNoType ->
                                exprCheck env expr tyC >>> go rest (Map.insert ident True seenMap)
                            VariantFieldMissing ->
                                CheckErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeVariant fields))
                    SomePatternData pat ->
                        case lookupVariantField ident fields of
                            VariantFieldExistSomeType ty ->
                                let res = bindPattern env pat ty >>= \env' -> exprCheck env' expr tyC
                                in res >>> go rest (Map.insert ident True seenMap)
                            VariantFieldExistNoType ->
                                CheckErr ERROR_UNEXPECTED_NON_NULLARY_VARIANT_PATTERN
                            VariantFieldMissing ->
                                CheckErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeVariant fields))
            _ -> CheckErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeVariant fields))

checkMatchCasesList :: Env -> [MatchCase] -> Type -> Type -> CheckResult
checkMatchCasesList env cases (TypeList ty) tyC =
    go cases
  where
    go :: [MatchCase] -> CheckResult
    go [] = CheckOk
    go (AMatchCase pat expr : rest) =
        case pat of
            PatternList pats ->
                let bindAll e [] = InferOk e
                    bindAll e (p:ps) =
                        bindPattern e p ty >>= \e' -> bindAll e' ps
                in case bindAll env pats of
                     InferErr err -> CheckErr err
                     InferOk env' -> exprCheck env' expr tyC >>> go rest
            PatternCons patH patT ->
                case bindPattern env patH ty of
                    InferErr err -> CheckErr err
                    InferOk env' ->
                        case bindPattern env' patT (TypeList ty) of
                            InferErr err -> CheckErr err
                            InferOk env'' -> exprCheck env'' expr tyC >>> go rest
            _ -> CheckErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE_M pat (TypeList ty))

checkMatchCasesBool :: Env -> [MatchCase] -> Type -> CheckResult
checkMatchCasesBool env cases tyC =
    go cases False False
  where
    go [] seenTrue seenFalse
      | not seenTrue  = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases)
      | not seenFalse = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases)
      | otherwise     = CheckOk

    go (AMatchCase pat expr : rest) seenTrue seenFalse =
      case pat of
        PatternTrue  ->
          exprCheck env expr tyC >>> go rest True seenFalse
        PatternFalse ->
          exprCheck env expr tyC >>> go rest seenTrue True
        PatternVar x ->
          let env' = (x, TypeBool):env
          in exprCheck env' expr tyC >>> go rest True True
        _ ->
          CheckErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE_M pat TypeBool)

checkMatchCasesNat :: Env -> [MatchCase] -> Type -> CheckResult
checkMatchCasesNat env cases tyC =
    go cases False False
  where
    go [] seenZero seenSucc
      | not seenZero = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases)
      | not seenSucc = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases)
      | otherwise    = CheckOk

    go (AMatchCase pat expr : rest) seenZero seenSucc =
      case pat of
        PatternInt 0 ->
          exprCheck env expr tyC >>> go rest True seenSucc
        PatternSucc p ->
          case bindPattern env p TypeNat of
            InferErr err -> CheckErr err
            InferOk env' ->
              exprCheck env' expr tyC >>> go rest seenZero True
        PatternVar x ->
          let env' = (x, TypeNat):env
          in exprCheck env' expr tyC >>> go rest True True
        _ ->
          CheckErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE_M pat TypeNat)

checkMatchCasesUnit :: Env -> [MatchCase] -> Type -> CheckResult
checkMatchCasesUnit env cases tyC =
    go cases False
  where
    go [] seenUnit
      | not seenUnit = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases)
      | otherwise    = CheckOk

    go (AMatchCase pat expr : rest) seenUnit =
      case pat of
        PatternUnit ->
          exprCheck env expr tyC >>> go rest True
        PatternVar x ->
          let env' = (x, TypeUnit):env
          in exprCheck env' expr tyC >>> go rest True
        _ ->
          CheckErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE_M pat TypeUnit)

-- (-) PatternCastAs Pattern Type
-- (-) PatternAsc Pattern Type
-- (+) PatternVariant StellaIdent PatternData
-- (+) PatternInl Pattern
-- (+) PatternInr Pattern
-- (+) PatternTuple [Pattern]
-- (+) PatternRecord [LabelledPattern]
-- (+) PatternList [Pattern]
-- (+) PatternCons Pattern Pattern
-- (+) PatternFalse
-- (+) PatternTrue
-- (+) PatternUnit
-- (+) PatternInt Integer
-- (+) PatternSucc Pattern
-- (+) PatternVar StellaIdent
bindPattern :: Env -> Pattern -> Type -> InferResult Env

bindPattern env p@(PatternCastAs pat ty) t =
    InferErr (ERROR_PATTERN_NOT_SUPPORTED p t)

bindPattern env p@(PatternAsc pat ty) t =
    InferErr (ERROR_PATTERN_NOT_SUPPORTED p t)

bindPattern env (PatternVariant ident patData) (TypeVariant fields) =
    case patData of
        NoPatternData       ->
            case lookupVariantField ident fields of
                VariantFieldExistSomeType ty ->
                    InferErr ERROR_UNEXPECTED_NULLARY_VARIANT_PATTERN
                VariantFieldExistNoType ->
                    InferOk env
                VariantFieldMissing ->
                    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeVariant fields))
        SomePatternData pat ->
            case lookupVariantField ident fields of
                VariantFieldExistSomeType ty ->
                    bindPattern env pat ty
                VariantFieldExistNoType ->
                    InferErr ERROR_UNEXPECTED_NON_NULLARY_VARIANT_PATTERN
                VariantFieldMissing ->
                    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeVariant fields))
bindPattern _   (PatternVariant ident patData) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternInl p) (TypeSum t1 _) =
    bindPattern env p t1
bindPattern _   (PatternInl _) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternInr p) (TypeSum _ t2) =
    bindPattern env p t2
bindPattern _   (PatternInr _) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternTuple pats) (TypeTuple tys) =
    let bindAll e [] [] = InferOk e
        bindAll e (p:ps) (t:ts) =
            bindPattern e p t >>= \e' -> bindAll e' ps ts
        bindAll _ _ _ = InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeTuple tys))
    in bindAll env pats tys
bindPattern _   (PatternTuple _) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternRecord pats) (TypeRecord fields) =
    let identToType = [(i, ty)  | ARecordFieldType i ty <- fields]
        bindAll e [] = InferOk e
        bindAll e ((ALabelledPattern ident identPat):ps) =
            case lookup ident identToType of
                Just ty ->
                    bindPattern e identPat ty >>= \e' -> bindAll e' ps
                Nothing -> InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeRecord fields))
    in bindAll env pats
bindPattern _   (PatternRecord _) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternList pats) (TypeList ty) =
    let bindAll e [] = InferOk e
        bindAll e (p:ps) =
            bindPattern e p ty >>= \e' -> bindAll e' ps
    in bindAll env pats
bindPattern _   (PatternList _) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternCons patH patT) (TypeList ty) =
    case bindPattern env patH ty of
        InferErr err -> InferErr err
        InferOk env' ->
            bindPattern env' patT (TypeList ty)
bindPattern _   (PatternCons _ _) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env PatternFalse TypeBool =
    InferOk env
bindPattern _   PatternFalse ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env PatternTrue TypeBool =
    InferOk env
bindPattern _   PatternTrue ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env PatternUnit TypeUnit =
    InferOk env
bindPattern _   PatternUnit ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

-- Надеюсь что парсер сделал за меня грязную работу и с остальными литерала не взлетит
bindPattern env (PatternInt n) TypeNat =
    InferOk env
bindPattern _   (PatternInt n) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternSucc n) TypeNat =
    bindPattern env n TypeNat
bindPattern _   (PatternSucc n) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternVar ident) t =
    InferOk (env ++ [(ident, t)])

-- ====== HELPERS ======

data VariantFieldLookupStatus
    = VariantFieldExistSomeType Type
    | VariantFieldExistNoType
    | VariantFieldMissing
  deriving (Eq, Ord, Show, Read)

-- Вспомогательная функция для поиска тега в TypeVariant
lookupVariantField :: StellaIdent -> [VariantFieldType] -> VariantFieldLookupStatus
lookupVariantField ident fields =
    let nameToOptType = [(n, t) | AVariantFieldType n t <- fields]
    in
        case lookup ident nameToOptType of
            Just (SomeTyping t)     -> VariantFieldExistSomeType t
            Just (NoTyping)         -> VariantFieldExistNoType
            Nothing                 -> VariantFieldMissing
