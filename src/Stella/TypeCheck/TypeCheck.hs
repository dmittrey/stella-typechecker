{-# LANGUAGE PatternSynonyms #-}

module Stella.TypeCheck.TypeCheck where

import Stella.TypeCheck.Error
import Stella.TypeCheck.Context
import Stella.TypeCheck.Subsumption

import Stella.Abs
import Stella.ErrM

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Maybe
import Data.List
import Prelude

-- TODO:
-- Перейти на do-нотацию
-- CI

-- Core, #nested-function-declarations, #nullary-functions
declCheck :: Env -> Decl -> (CheckResult, Env)
declCheck env (DeclFun anns funIdent@(StellaIdent funName) paramsAnn retTy throwTy decls expr) =
    let
        -- вычисляем тип возвращаемого значения
        resultTy = case retTy of
                      NoReturnType      -> TypeUnit
                      SomeReturnType ty -> ty

        -- тип самой функции
        funTy    = TypeFun [t | AParamDecl _ t <- paramsAnn] resultTy

        -- функция должна быть доступна самой себе для рекурсии
        envWithFun = env { envVars = (funIdent, funTy) : envVars env }

        -- добавляем параметры в локальное окружение (новый слой)
        env' = envWithFun { envVars = [(pIdent, t) | AParamDecl pIdent t <- paramsAnn] ++ envVars envWithFun }

        -- сначала проверяем внутренние функции/decls
        (resInner, envInner) = foldl step (CheckOk, env') decls

        -- проверка тела функции
        resBody = exprCheck envInner expr resultTy

        -- проверка основной функции main (правильная арность)
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

declCheck e (DeclExceptionType _) = (CheckOk, e)
declCheck e (DeclExceptionVariant _ _) = (CheckOk, e)

declCheck e d = (CheckErr (ERROR_DECL_CHECK_NOT_IMPLEMENTED d), e)

exprCheck :: Env -> Expr -> Type -> CheckResult

-- ====== T-True ======
exprCheck env ConstTrue t
    | isSubtyping env =
        if (TypeBool <: t)
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_SUBTYPE TypeBool t)
    | otherwise       =
        if (t == TypeBool)
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION ConstTrue TypeBool t)

-- ====== T-False ======
exprCheck env ConstFalse t
    | isSubtyping env =
        if (TypeBool <: t)
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_SUBTYPE TypeBool t)
    | otherwise       =
        if (t == TypeBool)
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION ConstFalse TypeBool t)

-- ====== T-If ======
exprCheck env (If e1 e2 e3) t =
    exprCheck env e1 TypeBool
    >>> exprCheck env e2 t
    >>> exprCheck env e3 t

-- ====== T-Zero ======
exprCheck env (ConstInt 0) t
    | isSubtyping env =
        if (TypeNat <: t)
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_SUBTYPE TypeNat t)
    | otherwise       =
        if (t == TypeNat)
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (ConstInt 0) TypeNat t)

-- ====== T-Succ ======
exprCheck env (Succ e) t
    | isSubtyping env =
        if (TypeNat <: t)
            then exprCheck env e TypeNat
            else CheckErr (ERROR_UNEXPECTED_SUBTYPE TypeNat t)
    | otherwise       =
        if (t == TypeNat)
            then exprCheck env e TypeNat
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (Succ e) TypeNat t)

-- ====== T-Pred ======
exprCheck env (Pred e) t
    | isSubtyping env =
        if (TypeNat <: t)
            then exprCheck env e TypeNat
            else CheckErr (ERROR_UNEXPECTED_SUBTYPE TypeNat t)
    | otherwise       =
        if (t == TypeNat)
            then exprCheck env e TypeNat
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (Pred e) TypeNat t)

-- ====== T-IsZero ======
exprCheck env (IsZero e) t
    | isSubtyping env =
        if (TypeBool <: t)
            then exprCheck env e TypeNat
            else CheckErr (ERROR_UNEXPECTED_SUBTYPE TypeBool t)
    | otherwise       =
        if (t == TypeBool)
            then exprCheck env e TypeNat
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (IsZero e) TypeBool t)

-- ====== T-NatRec ======
exprCheck env (NatRec n z s) ty =
    exprCheck env n TypeNat
    >>> exprCheck env z ty
    >>> exprCheck env s (TypeFun [TypeNat] (TypeFun [ty] ty))

-- ====== T-Var ======
exprCheck env (Var ident) t
    | isSubtyping env =
        case lookup ident (envVars env) of
            Just ty ->
                case (ty, t) of
                    (TypeFun lParams lRet, TypeFun rParams rRet)
                        | length lParams /= length rParams -> CheckErr ERROR_INCORRECT_NUMBER_OF_ARGUMENTS
                        | ty <: t                         -> CheckOk
                        | otherwise                        -> CheckErr (ERROR_UNEXPECTED_SUBTYPE ty t)
                    _ | ty <: t                           -> CheckOk
                      | otherwise                          -> CheckErr (ERROR_UNEXPECTED_SUBTYPE ty t)
            Nothing -> CheckErr (ERROR_UNDEFINED_VARIABLE ident)
    | otherwise =
        case lookup ident (envVars env) of
            Just ty ->
                case (ty, t) of
                    (TypeFun lParams lRet, TypeFun rParams rRet)
                        | length lParams /= length rParams -> CheckErr ERROR_INCORRECT_NUMBER_OF_ARGUMENTS
                        | ty == t                          -> CheckOk
                        | otherwise                        -> CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (Var ident) ty t)
                    _ | ty == t                             -> CheckOk
                      | otherwise                            -> CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (Var ident) ty t)
            Nothing -> CheckErr (ERROR_UNDEFINED_VARIABLE ident)


-- ====== T-Abs ======
exprCheck env (Abstraction params e) (TypeFun expParamTys retTy) =
    case checkParams env params expParamTys of
        (CheckOk, newEnv) -> exprCheck newEnv e retTy
        (CheckErr err, _) -> CheckErr err
-- Ошибка если тип не TypeFun
exprCheck env expr@(Abstraction _ _) t =
    CheckErr (ERROR_UNEXPECTED_LAMBDA expr t)

-- ====== T-App ======
exprCheck env (Application t1 args) expectedTy
    | isSubtyping env =
        case exprInfer env t1 of
            InferOk (TypeFun paramTys resultTy)
                | resultTy <: expectedTy ->
                    checkArgs env args paramTys
                | otherwise ->
                    CheckErr (ERROR_UNEXPECTED_SUBTYPE resultTy expectedTy)
            InferOk _ ->
                CheckErr (ERROR_NOT_A_FUNCTION t1)
            InferErr err ->
                CheckErr err
    | otherwise       =
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
exprCheck env ConstUnit t
    | isSubtyping env =
        if (TypeUnit <: t)
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_SUBTYPE TypeBool t)
    | otherwise       =
        if (t == TypeUnit)
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (ConstUnit) TypeUnit t)

-- ====== T-Seq ======
exprCheck env (Sequence e1 e2) t =
    exprCheck env e1 TypeUnit
    >>> exprCheck env e2 t

-- ====== T-Asc ======
exprCheck env (TypeAsc e ty) t =
    exprCheck env e t

-- ====== T-TryCastAs ======
    -- TODO What to do with cast expr?
exprCheck env (TryCastAs castExpr castTy pat succExpr catchExpr) ty =
    bindPattern env pat castTy >>= \e' -> exprCheck e' succExpr ty
    >>> exprCheck env catchExpr ty

-- ====== T-CastAs ======
exprCheck env (TypeCast e targetTy) ty =
    exprCheck env (TypeCast e targetTy) ty

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
                case bindPattern envAcc p tyAnn of
                    InferOk env' ->
                        case exprCheck env' e tyAnn of
                            CheckOk     -> InferOk env'
                            CheckErr er -> InferErr er
                    InferErr er -> InferErr er
            _ -> InferErr (ERROR_AMBIGUOUS_PATTERN_TYPE pat)
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

exprCheck _ expr@(Variant _ _) _ = CheckErr ERROR_UNEXPECTED_VARIANT

-- ====== T-Head ======
exprCheck env (Head expr) ty =
    exprCheck env expr (TypeList ty)

-- ====== T-Tail ======
exprCheck env (Tail expr) (TypeList ty) =
    exprCheck env expr (TypeList ty)

exprCheck env e@(Tail expr) ty =
    CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e (TypeList ty) ty)

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

exprCheck env e@(ConsList _ _) ty
    | isSubtyping env =
        case exprInfer env e of
            InferOk inferredTy ->
                if inferredTy <: ty
                   then CheckOk
                   else CheckErr (ERROR_UNEXPECTED_SUBTYPE inferredTy ty)
            InferErr err -> CheckErr err
    | otherwise = CheckErr (ERROR_UNEXPECTED_LIST e)

-- ====== T-Fix ======
exprCheck env (Fix expr@(Abstraction params e)) ty =
    exprCheck env expr (TypeFun [ty] ty)

exprCheck env (Fix expr@(Var ident)) ty =
    exprCheck env expr (TypeFun [ty] ty)

exprCheck env (Fix expr) ty = CheckErr (ERROR_NOT_A_FUNCTION expr)

-- ====== T-Case ======
exprCheck env (Match t []) tyC =
    CheckErr ERROR_ILLEGAL_EMPTY_MATCHING

-- При проверке против типа, я должен вывести тип терма, а потом подставляя match case проверять против типа tyC
exprCheck env (Match t cases) tyC =
    case exprInfer env t of
        InferErr err -> CheckErr err
        InferOk ty  -> checkMatchCases env cases ty tyC

-- ====== T-Natural ======
exprCheck env (ConstInt n) t
    | isSubtyping env =
        if (TypeNat <: t)
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_SUBTYPE TypeNat t)
    | otherwise       =
        if (t == TypeNat)
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (ConstInt n) TypeNat t)

-- ====== T-Add ======
exprCheck env (Add e1 e2) t
    | isSubtyping env =
        if (TypeNat <: t)
            then exprCheck env e1 TypeNat
                >>> exprCheck env e2 TypeNat
            else CheckErr (ERROR_UNEXPECTED_SUBTYPE TypeNat t)
    | otherwise       =
        if (t == TypeNat)
            then exprCheck env e1 TypeNat
                >>> exprCheck env e2 TypeNat
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (Add e1 e2) TypeNat t)

-- ====== T-Equal ======
exprCheck env (Equal e1 e2) t
    | isSubtyping env =
        if (TypeBool <: t)
            then case exprInfer env e1 of
                InferOk ty1 ->
                    exprCheck env e2 ty1
                InferErr err ->
                    CheckErr err
            else CheckErr (ERROR_UNEXPECTED_SUBTYPE TypeBool t)
    | otherwise       =
        if (t == TypeBool)
            then case exprInfer env e1 of
                InferOk ty1 ->
                    exprCheck env e2 ty1
                InferErr err ->
                    CheckErr err
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (Equal e1 e2) TypeBool t)

-- ====== T-Ref ======
exprCheck env e@(Ref _) t
    | isSubtyping env =
        case exprInfer env e of
            InferOk inferredTy ->
                if inferredTy <: t
                   then CheckOk
                   else CheckErr (ERROR_UNEXPECTED_SUBTYPE inferredTy t)
            InferErr err -> CheckErr err

-- без подтипирования
exprCheck env (Ref e) (TypeRef ty) =
    exprCheck env e ty

exprCheck _ e@(Ref _) t =
    CheckErr (ERROR_UNEXPECTED_REFERENCE)


-- ====== T-Deref ======
exprCheck env (Deref e) t =
    exprCheck env e (TypeRef t)

-- ====== T-Assign ======
exprCheck env (Assign el er) t
    | isSubtyping env =
        if (TypeUnit <: t)
            then case exprInfer env el of
                InferOk (TypeRef ty) ->
                    exprCheck env er ty
                InferOk _ ->
                    CheckErr (ERROR_NOT_A_REFERENCE el)
                InferErr err ->
                    CheckErr err
            else CheckErr (ERROR_UNEXPECTED_SUBTYPE TypeUnit t)
    | otherwise       =
        if (t == TypeUnit)
            then case exprInfer env el of
                InferOk (TypeRef ty) ->
                    exprCheck env er ty
                InferOk _ ->
                    CheckErr (ERROR_NOT_A_REFERENCE el)
                InferErr err ->
                    CheckErr err
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (Assign el er) TypeUnit t)

-- ====== T-Memory ======
exprCheck env (ConstMemory (MemoryAddress adrStr)) (TypeRef _) =
    CheckOk

exprCheck env (ConstMemory (MemoryAddress adrStr)) ty =
    CheckErr (ERROR_UNEXPECTED_MEMORY_ADDRESS adrStr)

-- ====== T-Error ======
exprCheck env Panic t =
    CheckOk

-- ====== T-Exn ======
exprCheck env (Throw t1) t =
    case envExn env of
        ExnTypeNotDeclared ->
            CheckErr (ERROR_EXCEPTION_TYPE_NOT_DECLARED t1)
        ExnTypeDecl ty -> do
            exprCheck env t1 ty
            if TypeBottom <: t
               then CheckOk
               else CheckErr (DEBUG TypeBottom)
        ExnOpenVariant tv -> do
            exprCheck env t1 (TypeVariant tv)
            if TypeBottom <: t
               then CheckOk
               else CheckErr (DEBUG TypeBottom)

-- ====== T-TryWith ======
exprCheck env (TryWith e1 e2) t =
    exprCheck env e1 t
    >>> exprCheck env e2 t

-- ====== T-TryCatch ======
exprCheck env (TryCatch e1 pat e2) t =
    exprCheck env e1 t
    >>> case envExn env of
        ExnTypeNotDeclared ->
            CheckErr (ERROR_EXCEPTION_TYPE_NOT_DECLARED e1)
        ExnTypeDecl ty ->
            bindPattern env pat ty >>= \e' -> exprCheck e' e2 t
        ExnOpenVariant tv ->
            bindPattern env pat (TypeVariant tv) >>= \e' -> exprCheck e' e2 t

-- Other

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
    case lookup ident (envVars env) of
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

-- ====== T-Asc ======
exprInfer env (TypeAsc e ty) =
    case exprCheck env e ty of
        CheckOk ->
            InferOk ty
        CheckErr err ->
            InferErr err

-- ====== T-TryCastAs ======
exprInfer env (TryCastAs castExpr castTy pat succExpr catchExpr) =
    case exprInfer env catchExpr of
        InferErr err ->
            InferErr err
        InferOk ty ->
            case bindPattern env pat castTy >>= \e' -> exprCheck e' succExpr ty of
                CheckErr err ->
                    InferErr err
                CheckOk ->
                    InferOk ty

-- ====== T-CastAs ======
exprInfer env (TypeCast _ targetTy) = InferOk targetTy

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
exprInfer env (Inl expr)
    | isAmbTyAsBot env  =
        case exprInfer env expr of
            InferOk ty ->
                InferOk (TypeSum ty TypeBottom)
            InferErr err ->
                InferErr err
    | otherwise         = InferErr (ERROR_AMBIGUOUS_SUM_TYPE expr)

-- ====== T-Inr ======
exprInfer env (Inr expr)
    | isAmbTyAsBot env  =
        case exprInfer env expr of
            InferOk ty ->
                InferOk (TypeSum TypeBottom ty)
            InferErr err ->
                InferErr err
    | otherwise         = InferErr (ERROR_AMBIGUOUS_SUM_TYPE expr)

-- ====== T-Variant ======
    -- TODO Там надо добавить как есть, тк он потом по отношению подтипизации превратиться в другой
exprInfer env expr@(Variant ident exprData)
    | isAmbTyAsBot env  = InferOk TypeBottom
    | isSubtyping env   = 
        case exprData of
            NoExprData ->
                InferOk (TypeVariant [(AVariantFieldType ident NoTyping)])
            SomeExprData e ->
                case exprInfer env e of
                    InferErr err ->
                        InferErr err
                    InferOk ty ->
                        InferOk (TypeVariant [(AVariantFieldType ident (SomeTyping ty))])
    | otherwise         = InferErr (ERROR_AMBIGUOUS_VARIANT_TYPE expr)

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
exprInfer env (List [])
    | isAmbTyAsBot env  = InferOk (TypeList TypeBottom)
    | isSubtyping env   = InferOk (TypeList TypeBottom)
    | otherwise         = InferErr ERROR_AMBIGUOUS_LIST_TYPE

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

-- ====== T-Case ======
exprInfer env (Match t []) =
    InferErr ERROR_ILLEGAL_EMPTY_MATCHING

-- При проверке против типа, я должен вывести тип терма, а потом подставляя match case вывести тип и проверить на эквивалентность
exprInfer env (Match t cases) =
    case exprInfer env t of
        InferErr err -> 
            InferErr err
        InferOk ty  -> 
            inferMatchCases env cases ty

-- ====== T-Natural ======
exprInfer _ (ConstInt n) = InferOk TypeNat -- #natural-literals

-- ====== T-Ref ======
exprInfer env (Ref e) =
    case exprInfer env e of
        InferOk ty ->
            InferOk (TypeRef ty)
        InferErr err ->
            InferErr err

-- ====== T-Deref ======
exprInfer env (Deref e) =
    case exprInfer env e of
        InferOk (TypeRef ty) -> InferOk ty
        InferOk ty           -> InferErr (ERROR_NOT_A_REFERENCE e)
        InferErr err         -> InferErr err

-- ====== T-Assign ======
exprInfer env (Assign el er) =
    case exprInfer env el of
        InferOk (TypeRef ty) ->
            case exprCheck env er ty of
                CheckOk      -> InferOk TypeUnit
                CheckErr err -> InferErr err
        InferOk _ ->
            InferErr (ERROR_NOT_A_REFERENCE el)
        InferErr err ->
            InferErr err

-- ====== T-Memory ======
exprInfer env (ConstMemory (MemoryAddress adrStr))
    | isAmbTyAsBot env  = InferOk (TypeRef TypeBottom)
    | otherwise         = InferErr ERROR_AMBIGUOUS_REFERENCE_TYPE

-- ====== T-Error ======
exprInfer env Panic
    | isAmbTyAsBot env  = InferOk TypeBottom
    | otherwise         = InferErr ERROR_AMBIGUOUS_PANIC_TYPE

-- ====== T-Exn ======
exprInfer env (Throw _)
    | isAmbTyAsBot env  = InferOk TypeBottom
    | otherwise         = InferErr ERROR_AMBIGUOUS_THROW_TYPE

-- ====== T-TryWith ======
exprInfer env (TryWith e1 e2) =
    case exprInfer env e1 of
        InferErr err ->
            InferErr err
        InferOk ty ->
            case exprCheck env e2 ty of
                CheckOk ->
                    InferOk ty
                CheckErr err ->
                    InferErr err

-- ====== T-TryCatch ======
exprInfer env (TryCatch e1 pat e2) =
    case exprInfer env e1 of
        InferErr err ->
            InferErr err
        InferOk ty1 ->
            case envExn env of
                ExnTypeNotDeclared ->
                    InferErr (ERROR_EXCEPTION_TYPE_NOT_DECLARED e1)
                ExnTypeDecl ty ->
                    bindPattern env pat ty >>= \e' -> 
                        case exprCheck e' e2 ty1 of
                            CheckErr err ->
                                InferErr err
                            CheckOk ->
                                InferOk ty1
                ExnOpenVariant tv ->
                    bindPattern env pat (TypeVariant tv) >>= \e' -> 
                        case exprCheck e' e2 ty1 of
                            CheckErr err ->
                                InferErr err
                            CheckOk ->
                                InferOk ty1

-- Other

exprInfer _ e = InferErr (ERROR_EXPR_INFER_NOT_IMPLEMENTED e)

inferMatchCases :: Env -> [MatchCase] -> Type -> InferResult Type
inferMatchCases env cases@(AMatchCase pat expr : rest) ty =
    let res = bindPattern env pat ty >>= \env' -> exprInfer env' expr
    in case res of
        InferErr err ->
            InferErr err
        InferOk tyC ->
            case checkMatchCases env cases ty tyC of
                CheckErr err ->
                    InferErr err
                CheckOk ->
                    InferOk tyC

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
-- (+) TypeTop
-- (+) TypeBottom
-- (+) TypeRef Type
-- (+) TypeVar StellaIdent
checkMatchCases :: Env -> [MatchCase] -> Type -> Type -> CheckResult

-- TypeAuto
checkMatchCases env cases TypeAuto tyC =
    CheckErr (ERROR_MATCH_NOT_SUPPORTED TypeAuto)

-- TypeForAll
checkMatchCases env cases t@(TypeForAll idents ty) tyC =
    CheckErr (ERROR_MATCH_NOT_SUPPORTED t)

-- TypeRec
checkMatchCases env cases t@(TypeRec ident ty) tyC =
    CheckErr (ERROR_MATCH_NOT_SUPPORTED t)

-- TypeSum
checkMatchCases env cases (TypeSum t1 t2) tyC =
    checkMatchCasesSum env cases (TypeSum t1 t2) tyC

-- TypeVariant
checkMatchCases env cases (TypeVariant fields) tyC =
    checkMatchCasesVariant env cases (TypeVariant fields) tyC

-- TypeBool
checkMatchCases env cases TypeBool tyC =
    checkMatchCasesBool env cases tyC

-- TypeNat
checkMatchCases env cases TypeNat tyC =
    checkMatchCasesNat env cases tyC

-- TypeList
checkMatchCases env cases (TypeList ty) tyC =
    checkMatchCasesList env cases (TypeList ty) tyC

-- TypeRecord
checkMatchCases env cases (TypeRecord fields) tyC =
    checkMatchCasesRecord env cases (TypeRecord fields) tyC

-- TypeList
checkMatchCases env cases (TypeTuple tys) tyC =
    checkMatchCasesTuple env cases (TypeTuple tys) tyC

-- Fallback
checkMatchCases env cases ty tyC =
    checkMatchCasesGeneric env cases ty tyC

checkMatchCasesTuple :: Env -> [MatchCase] -> Type -> Type -> CheckResult
checkMatchCasesTuple env cases t@(TypeTuple tys) tyC =
    go cases False
  where
    go [] seenAll
      | not seenAll = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS NotSeenAllTuple)
      | otherwise   = CheckOk

    go (AMatchCase pat expr : rest) seenAll =
        case pat of
          PatternTuple pats ->
              if length pats /= length tys
              then CheckErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeTuple tys))
              else
                case bindAll env pats tys of
                  InferErr err  -> CheckErr err
                  InferOk env'  -> exprCheck env' expr tyC >>> go rest True

          PatternVar _ ->
              bindPattern env pat t >>= \env' -> exprCheck env' expr tyC >>> go rest True

          _ ->
              bindPattern env pat t >>= \env' -> exprCheck env' expr tyC >>> go rest False

    -- bindAll: последовательно привязывает список паттернов к списку типов
    bindAll :: Env -> [Pattern] -> [Type] -> InferResult Env
    bindAll e [] [] = InferOk e
    bindAll e (p:ps) (ty:tys') =
        bindPattern e p ty >>= \e' -> bindAll e' ps tys'
    bindAll _ _ _ = InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeTuple tys))


checkMatchCasesRecord :: Env -> [MatchCase] -> Type -> Type -> CheckResult
checkMatchCasesRecord env cases t@(TypeRecord fields) tyC =
    go cases False
  where
    identToType = [(i, ty) | ARecordFieldType i ty <- fields]

    go [] seenAll
      | not seenAll = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS NotSeenAllRecord)
      | otherwise   = CheckOk

    go (AMatchCase pat expr : rest) seenAll =
        case pat of
          PatternRecord pats ->
              let checkAll [] = CheckOk
                  checkAll (ALabelledPattern ident identPat : ps) =
                    case lookup ident identToType of
                      Just ty ->
                        checkMatchCases env [AMatchCase identPat expr] ty tyC >>> checkAll ps
                      Nothing ->
                        CheckErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE t)
                  res = checkAll pats
              in res >>> go rest True

          PatternVar ident ->
              let res = bindPattern env pat t >>= \env' -> exprCheck env' expr tyC
              in res >>> go rest True

          _ ->
              let res = bindPattern env pat t >>= \env' -> exprCheck env' expr tyC
              in res >>> go rest False



checkMatchCasesSum :: Env -> [MatchCase] -> Type -> Type -> CheckResult
checkMatchCasesSum env cases t@(TypeSum tl tr) tyC =
    go cases False False
  where
    go [] seenL seenR
      | not seenL = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS NotSeenLeftInjection)
      | not seenR = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS NotSeenRightInjection)
      | otherwise = CheckOk
    go (AMatchCase pat expr : rest) seenL seenR =
        case pat of
          PatternInl pl ->
              let res = checkMatchCases env [(AMatchCase pl expr)] tl tyC
              in res >>> go rest True seenR
          PatternInr pr ->
              let res = checkMatchCases env [(AMatchCase pr expr)] tr tyC
              in res >>> go rest seenL True
          PatternVar ident ->
              let res = bindPattern env pat t >>= \env' -> exprCheck env' expr tyC
              in res >>> go rest True True
          _ ->
              let res = bindPattern env pat t >>= \env' -> exprCheck env' expr tyC
              in res >>> go rest False False

checkMatchCasesVariant :: Env -> [MatchCase] -> Type -> Type -> CheckResult
checkMatchCasesVariant env cases (TypeVariant fields) tyC =
    let initialMap = Map.fromList [(ident, False) | AVariantFieldType ident ty <- fields]
  in
    go cases initialMap
  where
    go [] seenMap
      | not (all id (Map.elems seenMap)) = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS NotSeenAllLabels)
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
                    SomePatternData pat1 ->
                        case lookupVariantField ident fields of
                            VariantFieldExistSomeType ty ->
                                -- let res = checkMatchCases env [(AMatchCase pat1 expr)] ty tyC
                                let res = bindPattern env pat1 ty >>= \env' -> exprCheck env' expr tyC
                                in res >>> go rest (Map.insert ident True seenMap)
                            VariantFieldExistNoType ->
                                CheckErr ERROR_UNEXPECTED_NON_NULLARY_VARIANT_PATTERN
                            VariantFieldMissing ->
                                CheckErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeVariant fields))
            PatternVar ident ->
                let res = bindPattern env pat (TypeVariant fields) >>= \env' -> exprCheck env' expr tyC
                    allTrue = Map.map (const True) seenMap
                in res >>> go rest allTrue
            _ ->
                let res = bindPattern env pat (TypeVariant fields) >>= \env' -> exprCheck env' expr tyC
                    -- allTrue = Map.map (const True) seenMap
                in res >>> go rest seenMap

checkMatchCasesBool :: Env -> [MatchCase] -> Type -> CheckResult
checkMatchCasesBool env cases tyC =
    go cases False False
  where
    go [] seenTrue seenFalse
      | not seenTrue  = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS NotSeenTrue)
      | not seenFalse = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS NotSeenFalse)
      | otherwise     = CheckOk

    go (AMatchCase pat expr : rest) seenTrue seenFalse =
      case pat of
        PatternTrue  ->
            exprCheck env expr tyC >>> go rest True seenFalse
        PatternFalse ->
            exprCheck env expr tyC >>> go rest seenTrue True
        PatternVar ident ->
            let res = bindPattern env pat TypeBool >>= \env' -> exprCheck env' expr tyC
            in res >>> go rest True True
        _ ->
            let res = bindPattern env pat TypeBool >>= \env' -> exprCheck env' expr tyC
            in res >>> go rest False False

checkMatchCasesNat :: Env -> [MatchCase] -> Type -> CheckResult
checkMatchCasesNat env cases tyC =
    go cases False False
  where
    go [] seenZero seenSucc
      | not seenZero = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS NotSeenZero)
      | not seenSucc = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS NotSeenSucc)
      | otherwise    = CheckOk

    go (AMatchCase pat expr : rest) seenZero seenSucc =
      case pat of
        PatternInt 0 ->
          exprCheck env expr tyC >>> go rest True seenSucc
        PatternSucc (PatternInt n) ->
          exprCheck env expr tyC >>> go rest seenZero seenSucc
        PatternVar ident ->
          let res = bindPattern env pat TypeNat >>= \env' -> exprCheck env' expr tyC
          in res >>> go rest True True
        PatternSucc (PatternVar ident) ->
          let res = bindPattern env (PatternVar ident) TypeNat >>= \env' -> exprCheck env' expr tyC
          in res >>> go rest seenZero True
        _ ->
          let res = bindPattern env pat TypeNat >>= \env' -> exprCheck env' expr tyC
          in res >>> go rest False False

checkMatchCasesList :: Env -> [MatchCase] -> Type -> Type -> CheckResult
checkMatchCasesList env cases (TypeList ty) tyC =
    go cases False False
  where
    go [] emptyList consList
      | not emptyList = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS NotSeenEmptyList)
      | not consList = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS NotSeenConsList)
      | otherwise    = CheckOk

    go (AMatchCase pat expr : rest) emptyList consList =
      case pat of
        PatternList [] ->
            exprCheck env expr tyC >>> go rest True consList
        PatternCons patH patTail -> -- Nat List
            let res = checkMatchCases env [(AMatchCase patH expr)] ty tyC
                      >>> checkMatchCases env [(AMatchCase patTail expr)] (TypeList ty) tyC
            in res >>> go rest emptyList True
        PatternVar ident ->
            let res = bindPattern env pat (TypeList ty) >>= \env' -> exprCheck env' expr tyC
            in res >>> go rest True True
        _ ->
          let res = bindPattern env pat (TypeList ty) >>= \env' -> exprCheck env' expr tyC
          in res >>> go rest False False

checkMatchCasesGeneric :: Env -> [MatchCase] -> Type -> Type -> CheckResult
checkMatchCasesGeneric env cases ty tyC =
    go cases
  where
    go [] = CheckOk
    go (AMatchCase pat expr : rest) =
        let res = bindPattern env pat ty >>= \env' -> exprCheck env' expr tyC
        in res >>> go rest

-- ====== Bind Type By Pattern ======

-- (+) PatternCastAs Pattern Type
-- (+) PatternAsc Pattern Type
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

bindPattern env (PatternCastAs pat castTy) ty
    | ty <: castTy  = bindPattern env pat castTy
    | otherwise     = InferErr (ERROR_UNEXPECTED_SUBTYPE ty castTy)

bindPattern env (PatternAsc pat ascTy) ty =
    bindPattern env pat ascTy

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

bindPattern env (PatternInt n) TypeNat =
    InferOk env
bindPattern _   (PatternInt n) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternSucc n) TypeNat =
    bindPattern env n TypeNat
bindPattern _   (PatternSucc n) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternVar ident) t =
    InferOk env { envVars = (ident, t) : envVars env }

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

-- | Проверка параметров для функций с подтипированием
checkParams :: Env -> [ParamDecl] -> [Type] -> (CheckResult, Env)
checkParams env [] [] = (CheckOk, env)
checkParams env ((AParamDecl ident actualTy):ps) (ty:tys)
    | length ps /= length tys =
        (CheckErr ERROR_UNEXPECTED_NUMBER_OF_PARAMETERS_IN_LAMBDA, env)
    | isSubtyping env && ty <: actualTy =
        let (res, env') = checkParams env ps tys
        in (res, env' { envVars = (ident, actualTy) : envVars env' })
    | not (isSubtyping env) && actualTy == ty =
        let (res, env') = checkParams env ps tys
        in (res, env' { envVars = (ident, actualTy) : envVars env' })
    | isSubtyping env && not (ty <: actualTy) =
        (CheckErr (ERROR_UNEXPECTED_SUBTYPE ty actualTy), env)
    | otherwise =
        (CheckErr (ERROR_UNEXPECTED_TYPE_FOR_PARAMETER ident ty actualTy), env)

updateEnvByParams :: Env -> [ParamDecl] -> Env
updateEnvByParams env params =
    env { envVars = envVars env ++ [(ident, t) | AParamDecl ident t <- params] }

checkArgs :: Env -> [Expr] -> [Type] -> CheckResult
checkArgs _   []     []     = CheckOk
checkArgs _   []     _      = CheckErr ERROR_INCORRECT_NUMBER_OF_ARGUMENTS
checkArgs _   _      []     = CheckErr ERROR_INCORRECT_NUMBER_OF_ARGUMENTS
checkArgs env (e:es) (ty:tys) =
  exprCheck env e ty
  >>> checkArgs env es tys