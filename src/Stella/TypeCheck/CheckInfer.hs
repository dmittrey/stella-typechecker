module Stella.TypeCheck.CheckInfer where

import Stella.TypeCheck.Error
import Stella.TypeCheck.Context
import Stella.TypeCheck.Subsumption
import Stella.TypeCheck.PatternMatching
import Stella.TypeCheck.Unification

import Stella.Abs
import Stella.ErrM

import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad (foldM)

-- Универсальная проверка на подтип или равенство типов
exprCheckConst :: Env -> Expr -> Type -> Type -> CheckResult
exprCheckConst _ _ (TypeTuple lTys) (TypeTuple rTys)
    | length lTys /= length rTys    = CheckErr ERROR_UNEXPECTED_TUPLE_LENGTH
exprCheckConst _ _ (TypeFun lp lr) (TypeFun rp rr)
    | length lp /= length rp    = CheckErr ERROR_INCORRECT_NUMBER_OF_ARGUMENTS
exprCheckConst env expr u1@(TypeVar _) expectedTy = do
    return (unify u1 expectedTy)
exprCheckConst env expr actualTy u2@(TypeVar _) = do
    return (unify actualTy u2)
exprCheckConst env expr actualTy expectedTy
    | (<:=) env actualTy expectedTy = CheckOk emptyUEqs
    | isSubtyping env               = CheckErr (ERROR_UNEXPECTED_SUBTYPE actualTy expectedTy)
    | otherwise                     = CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION actualTy expectedTy)

-- ====== Type Check ======
exprCheck :: Env -> Expr -> Type -> CheckResult

-- ====== T-True ======
exprCheck env ConstTrue t =
    exprCheckConst env ConstTrue TypeBool t

-- ====== T-False ======
exprCheck env ConstFalse t =
    exprCheckConst env ConstFalse TypeBool t

-- ====== T-If ======
exprCheck env (If e1 e2 e3) u = do
    c1 <- exprCheck env e1 TypeBool
    c2 <- exprCheck env e2 u
    c3 <- exprCheck env e3 u
    return (c1 <> c2 <> c3)

-- ====== T-Zero ======
exprCheck env (ConstInt 0) t =
    exprCheckConst env (ConstInt 0) TypeNat t

-- ====== T-Succ ======
exprCheck env (Succ e) t = do
    exprCheckConst env (Succ e) TypeNat t 
    <> exprCheck env e TypeNat

-- ====== T-Pred ======
exprCheck env (Pred e) t = do
    exprCheckConst env (Pred e) TypeNat t 
    <> exprCheck env e TypeNat

-- ====== T-IsZero ======
exprCheck env (IsZero e) t = do
    exprCheckConst env (IsZero e) TypeBool t 
    <> exprCheck env e TypeNat

-- ====== T-NatRec ======
exprCheck env (NatRec n z s) ty = do
    exprCheck env n TypeNat
    <> exprCheck env z ty
    <> exprCheck env s (TypeFun [TypeNat] (TypeFun [ty] ty))

-- ====== T-Var ======
exprCheck env (Var ident) t =
    case lookup ident (envVars env) of
        Just u2@(TypeVar uIdent) -> CheckOk (unify t u2)
        Just ty                  -> exprCheckConst env (Var ident) ty t
        Nothing                  -> CheckErr (ERROR_UNDEFINED_VARIABLE ident)

-- ====== T-Abs ======
exprCheck env (Abstraction params expr) ty@TypeTop
    | isSubtyping env =
        CheckOk emptyUEqs
exprCheck env term@(Abstraction params expr) u@(TypeVar ident) = do
    -- Составляем тип функции из params и u
    let paramTypes = [ t | AParamDecl _ t <- params ]
        tyFun = TypeFun paramTypes u
    -- Проверяем абстракцию на этот тип
    exprCheck env term tyFun

exprCheck env (Abstraction params expr) (TypeFun paramsTys retTy) =
    case checkParams env params paramsTys of
        (CheckOk eqsParams, newEnv) -> do
            eqsBody <- exprCheck newEnv expr retTy
            return (eqsParams <> eqsBody)
        (CheckErr err, _) -> CheckErr err
exprCheck env (Abstraction p e) t =
    CheckErr (ERROR_UNEXPECTED_LAMBDA (Abstraction p e))

-- ====== T-App ======
exprCheck env (Application term args) ty@TypeTop
    | isSubtyping env =
        CheckOk emptyUEqs
exprCheck env term@(Application t1 t2) u@(TypeVar ident) = do
    tyFun  <- exprInfer env t1
    tyArgs <- mapM (exprInfer env) t2
    return (unify tyFun (TypeFun tyArgs u))
exprCheck env (Application t1 args) expectedTy = do
    tyFun <- exprInfer env t1
    case tyFun of
        TypeFun paramTys resultTy ->
            checkArgs env args paramTys
            <> exprCheckConst env (Application t1 args) resultTy expectedTy
        TypeVar ident ->
            case lookup ident (envVars env) of
                Just (TypeFun paramTys resultTy)  ->
                    checkArgs env args paramTys
                    <> exprCheckConst env (Application t1 args) resultTy expectedTy
                Nothing -> CheckErr (ERROR_UNDEFINED_VARIABLE ident)
        t ->
            CheckErr (ERROR_NOT_A_FUNCTION t (Application t1 args))

-- ====== T-Unit ======
exprCheck env ConstUnit t =
    exprCheckConst env ConstUnit TypeUnit t

-- ====== T-Seq ======
exprCheck env (Sequence e1 e2) u@(TypeVar ident) = do
    c1 <- exprCheck env e1 TypeUnit
    c2 <- exprCheck env e2 u
    return (c1 <> c2)
exprCheck env (Sequence e1 e2) t = do
    exprCheck env e1 TypeUnit
    <> exprCheck env e2 t

-- ====== T-Asc ======
exprCheck env (TypeAsc e ty) t = do
    exprCheck env e ty
    <> exprCheckConst env e ty t

-- ====== T-TryCastAs ======
exprCheck env (TryCastAs castExpr castTy pat succExpr catchExpr) TypeTop
    | isSubtyping env = CheckOk emptyUEqs

exprCheck env (TryCastAs castExpr castTy pat succExpr catchExpr) ty = do
    _ <- exprInfer env castExpr
    env' <- bindPattern env pat castTy
    
    exprCheck env' succExpr ty
    <> exprCheck env catchExpr ty

-- ====== T-Let ======
exprCheck env (Let bindings expr) TypeTop
    | isSubtyping env = CheckOk emptyUEqs

exprCheck env (Let bindings expr) t = do
    env' <- foldM step env bindings
    exprCheck env' expr t
  where
    step envAcc (APatternBinding p e) = do
        ty <- exprInfer envAcc e
        bindPattern envAcc p ty

-- ====== T-LetRec ======
exprCheck env (LetRec bindings body) ty@(TypeVar u) = do
    tyExpr <- exprInfer env (LetRec bindings body)
    return (unify ty tyExpr)

exprCheck env (LetRec bindings body) TypeTop
    | isSubtyping env = CheckOk emptyUEqs

exprCheck env (LetRec bindings body) tyC = do
    env' <- foldM step env bindings
    exprCheck env' body tyC
  where
    step envAcc (APatternBinding pat e) =
        case pat of
            PatternAsc p tyAnn -> do
                env'' <- bindPattern envAcc p tyAnn
                exprCheck env'' e tyAnn
                return env''
            _ -> InferErr (ERROR_AMBIGUOUS_PATTERN_TYPE pat)

-- ====== T-Tuple ======
exprCheck env expr@(Tuple _) ty@(TypeVar u) = do
    tyExpr <- exprInfer env expr
    return (unify ty tyExpr)

exprCheck env (Tuple []) (TypeTuple []) =
    CheckOk emptyUEqs

exprCheck env (Tuple (e : es)) TypeTop
    | isSubtyping env = CheckOk emptyUEqs
exprCheck env (Tuple (e : es)) (TypeTuple (ty : tys))
    | length es /= length tys = CheckErr ERROR_UNEXPECTED_TUPLE_LENGTH
    | otherwise = exprCheck env e ty <> exprCheck env (Tuple es) (TypeTuple tys)

exprCheck env expression@(Tuple _) ty =
    CheckErr (ERROR_UNEXPECTED_TUPLE expression ty)

-- ====== T-DotTuple ======
exprCheck env e@(DotTuple _ _) ty@(TypeVar u) = do
    tyExpr <- exprInfer env e
    return (unify ty tyExpr)

exprCheck env (DotTuple expr idx) TypeTop
    | isSubtyping env = CheckOk emptyUEqs

exprCheck env expression@(DotTuple expr idx) ty =
    case exprInfer env expr of
        InferOk (TypeTuple tys)
            | idx <= 0                          -> CheckErr (ERROR_TUPLE_INDEX_OUT_OF_BOUNDS expr idx)
            | (fromIntegral idx) > length tys   -> CheckErr (ERROR_TUPLE_INDEX_OUT_OF_BOUNDS expr idx)
            | otherwise                         -> exprCheckConst env expression (tys !! (fromIntegral idx - 1)) ty
        InferOk u@(TypeVar _)                   -> CheckOk (unify u ty)
        InferOk _                               -> CheckErr (ERROR_NOT_A_TUPLE expr)
        InferErr er                             -> CheckErr er

-- ====== T-Record ======
exprCheck env e@(Record _) ty@(TypeVar u) = do
    tyExpr <- exprInfer env e
    return (unify ty tyExpr)

exprCheck env (Record []) (TypeRecord []) =
    CheckOk emptyUEqs

exprCheck env (Record bindings) TypeTop
    | isSubtyping env = CheckOk emptyUEqs

exprCheck env (Record bindings) (TypeRecord fields) =
    let origBindingsLen = length bindings
        origFieldsLen   = length fields
        bindingsMap     = Map.fromList [(name, val) | ABinding name val <- bindings]
        fieldsMap       = Map.fromList [(name, ty)  | ARecordFieldType name ty <- fields]
        bindingNames    = Map.keysSet bindingsMap
        fieldNames      = Map.keysSet fieldsMap

        checkFields :: [(StellaIdent, Type)] -> CheckResult 
        checkFields [] = CheckOk emptyUEqs
        checkFields ((name, ty) : rest) = do
            case Map.lookup name bindingsMap of
                Just val -> (exprCheck env val ty <> checkFields rest)
                Nothing  -> CheckErr (DEBUG (TypeRecord fields) (TypeRecord fields))
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
exprCheck env e@(DotRecord _ _) ty@(TypeVar u) = do
    tyExpr <- exprInfer env e
    return (unify ty tyExpr)

exprCheck env (DotRecord expr ident) TypeTop
    | isSubtyping env = CheckOk emptyUEqs

exprCheck env (DotRecord expr ident) ty =
    case exprInfer env expr of
        InferOk (TypeRecord fields) ->
            let identToType = [(i, ty) | ARecordFieldType i ty <- fields]
            in case lookup ident identToType of
                Just actualTy -> exprCheckConst env expr actualTy ty
                Nothing       -> CheckErr (ERROR_UNEXPECTED_FIELD_ACCESS expr ident)
        InferOk _   -> CheckErr (ERROR_NOT_A_RECORD expr)
        InferErr er -> CheckErr er

-- ====== T-Inl ======
exprCheck env e@(Inl expr) ty@(TypeVar (StellaIdent u)) = do
    tyExpr <- exprInfer env expr
    return (unify ty (TypeSum tyExpr (TypeVar (StellaIdent (u ++ "_R")))))

exprCheck env (Inl expr) TypeTop
    | isSubtyping env = CheckOk emptyUEqs

exprCheck env (Inl expr) (TypeSum t1 t2) = exprCheck env expr t1

exprCheck env e@(Inl _) _ = CheckErr (ERROR_UNEXPECTED_INJECTION e)

-- -- ====== T-Inr ======
exprCheck env e@(Inr expr) ty@(TypeVar (StellaIdent u)) = do
    tyExpr <- exprInfer env expr
    return (unify ty (TypeSum (TypeVar (StellaIdent (u ++ "_L"))) tyExpr))

exprCheck env (Inr expr) TypeTop
    | isSubtyping env = CheckOk emptyUEqs

exprCheck env (Inr expr) (TypeSum t1 t2) = exprCheck env expr t2

exprCheck env e@(Inr _) _ = CheckErr (ERROR_UNEXPECTED_INJECTION e)

-- ====== T-Variant ======
exprCheck env e@(Variant ident exprData) ty@(TypeVar u) = do
    tyExpr <- exprInfer env e
    return (unify ty tyExpr)

exprCheck env (Variant _ _) TypeTop
    | isSubtyping env = CheckOk emptyUEqs

exprCheck env (Variant ident exprData) (TypeVariant fields) =
    let fieldNames = [name | AVariantFieldType name _ <- fields]
    in if length fieldNames /= Set.size (Set.fromList fieldNames)
        then CheckErr (ERROR_DUPLICATE_VARIANT_TYPE_FIELDS (TypeVariant fields))
       else case lookupVariantField ident fields of
            VariantFieldExistSomeType ty ->
                case exprData of
                    NoExprData       -> CheckErr (ERROR_MISSING_DATA_FOR_LABEL)
                    SomeExprData expr -> exprCheck env expr ty
            VariantFieldExistNoType ->
                case exprData of
                    NoExprData       -> CheckOk emptyUEqs
                    SomeExprData _   -> CheckErr (ERROR_UNEXPECTED_DATA_FOR_NULLARY_LABEL)
            VariantFieldMissing -> CheckErr (ERROR_UNEXPECTED_VARIANT_LABEL ident)

exprCheck _ e@(Variant _ _) _ = CheckErr ERROR_UNEXPECTED_VARIANT

-- ====== T-Head ======
exprCheck env e@(Head expr) ty@(TypeVar u) = do
    tyExpr <- exprInfer env e
    return (unify ty tyExpr)

exprCheck env (Head expr) TypeTop
    | isSubtyping env = CheckOk emptyUEqs

exprCheck env (Head expr) ty = exprCheck env expr (TypeList ty)

-- ====== T-Tail ======
exprCheck env e@(Tail expr) ty@(TypeVar u) = do
    tyExpr <- exprInfer env e
    return (unify ty tyExpr)

exprCheck env (Tail expr) TypeTop
    | isSubtyping env = CheckOk emptyUEqs

exprCheck env (Tail expr) (TypeList ty) = exprCheck env expr (TypeList ty)

exprCheck env e@(Tail expr) ty = CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (TypeList ty) ty)

-- ====== T-IsEmpty ======
exprCheck env (IsEmpty expr) t = do
    c1 <- exprCheckConst env (IsEmpty expr) TypeBool t
    ty <- exprInfer env expr
    case ty of
        TypeList _ -> CheckOk c1
        _          -> CheckErr (ERROR_NOT_A_LIST ty)

-- ====== T-List ======
exprCheck env (List (e : es)) ty@(TypeVar u) = do
    exprCheck env e ty <> exprCheck env (List es) ty

exprCheck env (List []) (TypeList ty) = CheckOk emptyUEqs

exprCheck env (List (e:[])) (TypeList ty) = exprCheck env e ty

exprCheck env (List (e:exprs)) TypeTop
    | isSubtyping env = CheckOk emptyUEqs

exprCheck env (List (e:exprs)) (TypeList ty) = do
    exprCheck env e ty <> exprCheck env (List exprs) (TypeList ty)

exprCheck env e@(List _) ty = CheckErr (ERROR_UNEXPECTED_LIST e)

-- ====== T-ConsList ======
exprCheck env e@(ConsList _ _) ty@(TypeVar u) = do
    tyExpr <- exprInfer env e
    return (unify ty tyExpr)

exprCheck env (ConsList e1 e2) TypeTop
    | isSubtyping env = CheckOk emptyUEqs

exprCheck env (ConsList e1 e2) (TypeList ty) = do
    exprCheck env e1 ty <> exprCheck env e2 (TypeList ty)

exprCheck env e@(ConsList _ _) ty = CheckErr (ERROR_UNEXPECTED_LIST e)

-- ====== T-Fix ======
exprCheck env (Fix expr) ty@(TypeVar u) = do
    tyExpr <- exprInfer env expr
    case tyExpr of
        TypeFun [t] u' -> 
            return (unify t u' <> unify ty t)
        TypeVar _ -> 
            return (unify tyExpr (TypeFun [tyExpr] ty))
        _ ->
            CheckErr (ERROR_NOT_A_FUNCTION ty expr)

exprCheck env (Fix expr@(Abstraction params e)) ty =
    exprCheck env expr (TypeFun [ty] ty)

exprCheck env (Fix expr@(Var ident)) ty =
    exprCheck env expr (TypeFun [ty] ty)

exprCheck env (Fix expr) ty = CheckErr (ERROR_NOT_A_FUNCTION ty expr)

-- ====== T-Case ======
exprCheck env e@(Match _ []) ty@(TypeVar u) = do
    tyExpr <- exprInfer env e
    return (unify ty tyExpr)

exprCheck env (Match _ []) _ = CheckErr ERROR_ILLEGAL_EMPTY_MATCHING

exprCheck env (Match t cases) tyC = do
    ty <- exprInfer env t
    checkMatchCases env cases ty tyC

-- -- ====== T-Natural ======
exprCheck env (ConstInt n) t =
    exprCheckConst env (ConstInt n) TypeNat t

-- ====== T-Add ======
exprCheck env (Add e1 e2) t = do
    exprCheckConst env (Add e1 e2) TypeNat t
    <> exprCheck env e1 TypeNat
    <> exprCheck env e2 TypeNat

-- ====== T-Equal ======
exprCheck env (Equal e1 e2) t = do
    ty <- exprInfer env e1
    c1 <- exprCheckConst env (Equal e1 e2) TypeBool t
    c2 <- exprCheck env e2 ty
    return (c1 <> c2)

-- ====== T-Ref ======
exprCheck env e@(Ref expr) ty@(TypeVar u) = do
    tyExpr <- exprInfer env e
    return (unify ty tyExpr)

exprCheck env (Ref e) TypeTop
    | isSubtyping env = CheckOk emptyUEqs

exprCheck env (Ref e) (TypeRef ty) = exprCheck env e ty

exprCheck _ e@(Ref _) t = CheckErr ERROR_UNEXPECTED_REFERENCE

-- ====== T-Deref ======
exprCheck env (Deref e) t = exprCheck env e (TypeRef t)

-- ====== T-Assign ======
exprCheck env (Assign el er) t = do
    c1 <- exprCheckConst env (Assign el er) TypeUnit t
    tyr <- exprInfer env el
    case tyr of
        TypeRef ty -> return (c1) <> exprCheck env er ty
        _          -> CheckErr (ERROR_NOT_A_REFERENCE el)

-- ====== T-Memory ======
exprCheck env e@(ConstMemory _) ty@(TypeVar u) = do
    tyExpr <- exprInfer env e
    return (unify ty tyExpr)

exprCheck env (ConstMemory (MemoryAddress _)) TypeTop
    | isSubtyping env = CheckOk emptyUEqs

exprCheck env (ConstMemory (MemoryAddress _)) (TypeRef _) = CheckOk emptyUEqs

exprCheck env (ConstMemory (MemoryAddress adrStr)) t =
    CheckErr (ERROR_UNEXPECTED_MEMORY_ADDRESS adrStr)

-- ====== T-Error ======
exprCheck _ Panic _ = CheckOk emptyUEqs

-- ====== T-Exn ======
exprCheck env e@(Throw t1) ty@(TypeVar u) = do
    tyExpr <- exprInfer env e
    return (unify ty tyExpr)

exprCheck env (Throw t1) _ =
    case envExn env of
        ExnTypeNotDeclared -> CheckErr (ERROR_EXCEPTION_TYPE_NOT_DECLARED t1)
        ExnTypeDecl ty     -> exprCheck env t1 ty
        ExnOpenVariant tv  -> exprCheck env t1 (TypeVariant tv)

-- ====== T-TryWith ======
exprCheck env (TryWith e1 e2) t = do
    case envExn env of
        ExnTypeNotDeclared -> CheckErr (ERROR_EXCEPTION_TYPE_NOT_DECLARED e1)
        _ -> exprCheck env e1 t <> exprCheck env e2 t

-- ====== T-TryCatch ======
exprCheck env (TryCatch e1 pat e2) t = do
    c1 <- exprCheck env e1 t
    c2 <- case envExn env of
        ExnTypeNotDeclared -> CheckErr (ERROR_EXCEPTION_TYPE_NOT_DECLARED e1)
        ExnTypeDecl tyExn  -> case bindPattern env pat tyExn of
                                InferErr err -> CheckErr err
                                InferOk e'   -> exprCheck e' e2 t
        ExnOpenVariant tv  -> case bindPattern env pat (TypeVariant tv) of
                                InferErr err -> CheckErr err
                                InferOk e'   -> exprCheck e' e2 t
    return (c1 <> c2)

-- Fallback
exprCheck _ e t = CheckErr (ERROR_EXPR_CHECK_NOT_IMPLEMENTED e t)

-- ====== Type Infer ======
exprInfer :: Env -> Expr -> InferResult Type

-- ====== T-True ======
exprInfer _ ConstTrue  = InferOk TypeBool

-- ====== T-False ======
exprInfer _ ConstFalse = InferOk TypeBool

-- ====== T-If ======
exprInfer env (If t1 t2 t3) = do
    checkForBool <- exprCheck env t1 TypeBool
    actualTy     <- exprInfer env t2
    checkBranch  <- exprCheck env t3 actualTy
    return actualTy

-- ====== T-Zero ======
exprInfer _ (ConstInt 0) = InferOk TypeNat

-- ====== T-Succ ======
exprInfer env (Succ e) = do
    exprCheck env e TypeNat
    return TypeNat

-- ====== T-Pred ======
exprInfer env (Pred e) = do
    exprCheck env e TypeNat
    return TypeNat

-- ====== T-IsZero ======
exprInfer env (IsZero e) = do
    exprCheck env e TypeNat
    return TypeBool

-- ====== T-NatRec ======
exprInfer env (NatRec n z s) = do
    exprCheck env n TypeNat
    
    actualT <- exprInfer env z
    exprCheck env s (TypeFun [TypeNat] (TypeFun [actualT] actualT))
    return actualT

-- ====== T-Var ======
exprInfer env (Var ident) =
    case lookup ident (envVars env) of
        Just t  -> InferOk t
        Nothing -> InferErr (ERROR_UNDEFINED_VARIABLE ident)

-- ====== T-Abs ======
exprInfer env (Abstraction params e) = do
    ty <- exprInfer (updateEnvByParams env params) e
    InferOk (TypeFun [t | AParamDecl _ t <- params] ty)

-- ====== T-App ======
exprInfer env (Application t1 args) = do
    ty <- exprInfer env t1
    case ty of
        TypeFun paramTys retTy -> do
            checkArgs env args paramTys
            return retTy
        u@(TypeVar ident) ->
            return u
        t ->
            InferErr (ERROR_NOT_A_FUNCTION t t1)

-- ====== T-Unit ======
exprInfer _ ConstUnit  = InferOk TypeUnit

-- ====== T-Seq ======
exprInfer env (Sequence e1 e2) = do
    exprCheck env e1 TypeUnit
    ty <- exprInfer env e2
    return ty

-- ====== T-Asc ======
exprInfer env (TypeAsc e ty) = do
    exprCheck env e ty
    return ty

-- ====== T-TryCastAs ======
exprInfer env (TryCastAs castExpr castTy pat succExpr catchExpr) = do
    dummyCheck <- exprInfer env castExpr

    actualTy <- exprInfer env catchExpr
    bindPattern env pat castTy >>= \e' -> exprCheck e' succExpr actualTy
    return actualTy

-- ====== T-Let ======
exprInfer env (Let bindings expr) = do
    env' <- foldM step env bindings
    ty <- exprInfer env' expr
    return ty
  where
    step :: Env -> PatternBinding -> InferResult Env
    step envAcc (APatternBinding p e) = do
        ty <- exprInfer envAcc e
        bindPattern envAcc p ty

-- -- ====== T-Tuple ======
exprInfer env (Tuple exprs) = do
    ty <- foldM step (TypeTuple []) exprs
    return ty
  where
    step :: Type -> Expr -> InferResult Type
    step (TypeTuple acc) e = do
        ty <- exprInfer env e
        InferOk (TypeTuple (acc ++ [ty]))

-- ====== T-DotTuple ======
exprInfer env expression@(DotTuple expr idx) =
    case exprInfer env expr of
        InferOk (TypeTuple tys)
            | idx <= 0                              -> InferErr (ERROR_TUPLE_INDEX_OUT_OF_BOUNDS expr idx)
            | (fromIntegral idx) > (length tys)     -> InferErr (ERROR_TUPLE_INDEX_OUT_OF_BOUNDS expr idx)
            | otherwise                             -> InferOk (tys !! (fromIntegral idx - 1))
        InferOk u@(TypeVar _)                       -> InferOk u
        InferOk _                                   -> InferErr (ERROR_NOT_A_TUPLE expr)
        InferErr err                                -> InferErr err

-- ====== T-Record ======
exprInfer env (Record bindings) =
    foldM step (TypeRecord []) bindings
  where
    step :: Type -> Binding -> InferResult Type
    step (TypeRecord acc) (ABinding ident e) = do
        ty <- exprInfer env e
        InferOk (TypeRecord (acc ++ [(ARecordFieldType ident ty)]))

-- ====== T-DotRecord ======
exprInfer env (DotRecord expr ident) =
    case exprInfer env expr of
        InferOk (TypeRecord fields) ->
            let identToType = [(ident, t) | ARecordFieldType ident t <- fields]
            in case lookup ident identToType of
                Just ty         -> InferOk ty
                Nothing         -> InferErr (ERROR_UNEXPECTED_FIELD_ACCESS expr ident)
        InferOk u@(TypeVar _)   -> InferOk u
        InferOk otherTy         -> InferErr (ERROR_NOT_A_RECORD expr)
        InferErr err            -> InferErr err

-- ====== T-Inl ======
exprInfer env (Inl expr)
    | isAmbTyAsBot env  = do
        ty <- exprInfer env expr
        InferOk (TypeSum ty TypeBottom)
    | isReconstruction env = do
        ty <- exprInfer env expr
        InferOk (TypeSum ty (TypeVar (StellaIdent "TR"))) --TODO Обернуть бы все в State
    | otherwise        = InferErr (ERROR_AMBIGUOUS_SUM_TYPE expr)
    

-- ====== T-Inr ======
exprInfer env (Inr expr)
    | isAmbTyAsBot env  = do
        ty <- exprInfer env expr
        InferOk (TypeSum TypeBottom ty)
    | isReconstruction env = do
        ty <- exprInfer env expr
        InferOk (TypeSum (TypeVar (StellaIdent "TL")) ty) --TODO Обернуть бы все в State
    | otherwise         = InferErr (ERROR_AMBIGUOUS_SUM_TYPE expr)

-- ====== T-Variant ======
exprInfer env expr@(Variant ident exprData)
    | isSubtyping env  =
        case exprData of
            NoExprData ->
                InferOk (TypeVariant [(AVariantFieldType ident NoTyping)])
            SomeExprData expr -> do
                ty <- exprInfer env expr
                InferOk (TypeVariant [(AVariantFieldType ident (SomeTyping ty))])
    | otherwise =
        InferErr (ERROR_AMBIGUOUS_VARIANT_TYPE expr)

-- ====== T-Head ======
exprInfer env (Head expr) = do
    ty <- exprInfer env expr
    case ty of
        TypeList ty         -> return ty
        u@(TypeVar ident)   -> return u
        ty                  -> InferErr (ERROR_NOT_A_LIST ty)

-- ====== T-Tail ======
exprInfer env (Tail expr) = do
    ty <- exprInfer env expr
    case ty of
        TypeList ty         -> return (TypeList ty)
        u@(TypeVar ident)   -> return u
        ty                  -> InferErr (ERROR_NOT_A_LIST ty)

-- ====== T-IsEmpty ======
exprInfer env (IsEmpty expr) = do
    ty <- exprInfer env expr
    case ty of
        TypeList ty         -> return TypeBool
        u@(TypeVar ident)   -> return u
        ty                  -> InferErr (ERROR_NOT_A_LIST ty)

-- ====== T-List ======
exprInfer env (List [])
    | isAmbTyAsBot env  = InferOk (TypeList TypeBottom)
    | otherwise         = InferErr (ERROR_AMBIGUOUS_LIST_TYPE)

exprInfer env (List (e:es)) = do
    tyElem <- exprInfer env e
    checkAll es tyElem
  where
    checkAll :: [Expr] -> Type -> InferResult Type
    checkAll [] ty = InferOk (TypeList ty)
    checkAll (x:xs) ty = do
        exprCheck env x ty
        checkAll xs ty

-- ====== T-ConsList ======
exprInfer env (ConsList e1 e2) = do
    tyHead <- exprInfer env e1
    exprCheck env e2 (TypeList tyHead)
    return (TypeList tyHead)

-- ====== T-Fix ======
exprInfer env (Fix expr) = do
    tyExpr <- exprInfer env expr
    case tyExpr of
        TypeFun [t] u -> return t
        TypeVar _     -> return tyExpr  -- оставляем как TypeVar, constraint создастся в exprCheck
        _             -> InferErr (ERROR_NOT_A_FUNCTION tyExpr expr)

-- ====== T-Case ======
exprInfer env (Match t []) =
    InferErr ERROR_ILLEGAL_EMPTY_MATCHING

-- При проверке против типа, я должен вывести тип терма, а потом подставляя match case вывести тип и проверить на эквивалентность
exprInfer env (Match t cases) = do
    ty <- exprInfer env t
    inferMatchCases env cases ty

-- ====== T-Natural ======
exprInfer _ (ConstInt n) = InferOk TypeNat -- #natural-literals

-- ====== T-Ref ======
exprInfer env (Ref e) = do
    ty <- exprInfer env e
    return (TypeRef ty)

-- ====== T-Deref ======
exprInfer env (Deref e) = do
    actualTy <- exprInfer env e
    case actualTy of
        (TypeRef ty) ->
            return ty
        u@(TypeVar ident) -> 
            return u
        ty ->
            InferErr (ERROR_NOT_A_REFERENCE e)

-- ====== T-Assign ======
exprInfer env (Assign el er) = do
    actualTy <- exprInfer env el
    case actualTy of
        TypeRef ty -> do
            exprCheck env er ty
            return TypeUnit
        u@(TypeVar ident) -> 
            return u
        _ ->
            InferErr (ERROR_NOT_A_REFERENCE el)

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
exprInfer env (TryWith e1 e2) = do
    case envExn env of
        ExnTypeNotDeclared -> InferErr (ERROR_EXCEPTION_TYPE_NOT_DECLARED e1)
        _ -> do
            ty <- exprInfer env e1
            exprCheck env e2 ty
            return ty

-- ====== T-TryCatch ======
exprInfer env (TryCatch e1 pat e2) = do
    ty1 <- exprInfer env e1
    case envExn env of
        ExnTypeNotDeclared ->
            InferErr (ERROR_EXCEPTION_TYPE_NOT_DECLARED e1)
        ExnTypeDecl ty -> do
            e' <- bindPattern env pat ty
            exprCheck e' e2 ty1
            return ty1
        ExnOpenVariant tv -> do
            e' <- bindPattern env pat (TypeVariant tv)
            exprCheck e' e2 ty1
            return ty1

exprInfer env (TypeCast e targetTy) = do
    _ <- exprInfer env e  -- type-check e only
    return targetTy

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
-- (+) TypeTop
-- (+) TypeBottom
-- (+) TypeRef Type
-- (+) TypeVar StellaIdent
checkMatchCases :: Env -> [MatchCase] -> Type -> Type -> CheckResult

-- TypeAuto
-- checkMatchCases env cases TypeAuto tyC =
--     CheckErr (ERROR_MATCH_NOT_SUPPORTED TypeAuto)

-- -- TypeForAll
-- checkMatchCases env cases t@(TypeForAll idents ty) tyC =
--     CheckErr (ERROR_MATCH_NOT_SUPPORTED t)

-- -- TypeRec
-- checkMatchCases env cases t@(TypeRec ident ty) tyC =
--     CheckErr (ERROR_MATCH_NOT_SUPPORTED t)

-- -- TypeSum
-- checkMatchCases env cases (TypeSum t1 t2) tyC =
--     checkMatchCasesSum env cases (TypeSum t1 t2) tyC

-- -- TypeVariant
-- checkMatchCases env cases (TypeVariant fields) tyC =
--     checkMatchCasesVariant env cases (TypeVariant fields) tyC

-- -- TypeBool
-- checkMatchCases env cases TypeBool tyC =
--     checkMatchCasesBool env cases tyC

-- Fallback
checkMatchCases env cases ty tyC =
    checkMatchCasesGeneric env cases ty tyC

-- checkMatchCasesSum :: Env -> [MatchCase] -> Type -> Type -> CheckResult
-- checkMatchCasesSum env cases t@(TypeSum tl tr) tyC =
--     go cases False False
--   where
--     go [] seenL seenR
--       | not seenL = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases)
--       | not seenR = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases)
--       | otherwise = CheckOk emptyUEqs

--     go (AMatchCase pat expr : rest) seenL seenR = do
--         case pat of
--           PatternInl pl -> do
--               envL <- bindPattern env pl tl
--               eqs1 <- exprCheck envL expr tyC
--               eqs2 <- go rest True seenR
--               return (eqs1 <> eqs2)

--           PatternInr pr -> do
--               envR <- bindPattern env pr tr
--               eqs1 <- exprCheck envR expr tyC
--               eqs2 <- go rest seenL True
--               return (eqs1 <> eqs2)

--           _ -> do
--               env' <- bindPattern env pat t
--               eqs1 <- exprCheck env' expr tyC
--               eqs2 <- go rest True True
--               return (eqs1 <> eqs2)

-- checkMatchCasesVariant :: Env -> [MatchCase] -> Type -> Type -> CheckResult
-- checkMatchCasesVariant env cases (TypeVariant fields) tyC =
--     let initialMap = Map.fromList [(ident, False) | AVariantFieldType ident ty <- fields]
--   in
--     go cases initialMap
--   where
--     go [] seenMap
--       | not (all id (Map.elems seenMap)) = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases)
--       | otherwise                        = CheckOk
--     go (AMatchCase pat expr : rest) seenMap =
--         case pat of
--             PatternVariant ident patData ->
--                 case patData of
--                     NoPatternData       ->
--                         case lookupVariantField ident fields of
--                             VariantFieldExistSomeType ty ->
--                                 CheckErr ERROR_UNEXPECTED_NULLARY_VARIANT_PATTERN
--                             VariantFieldExistNoType ->
--                                 exprCheck env expr tyC >>> go rest (Map.insert ident True seenMap)
--                             VariantFieldMissing ->
--                                 CheckErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeVariant fields))
--                     SomePatternData pat ->
--                         case lookupVariantField ident fields of
--                             VariantFieldExistSomeType ty ->
--                                 let res = bindPattern env pat ty >>= \env' -> exprCheck env' expr tyC
--                                 in res >>> go rest (Map.insert ident True seenMap)
--                             VariantFieldExistNoType ->
--                                 CheckErr ERROR_UNEXPECTED_NON_NULLARY_VARIANT_PATTERN
--                             VariantFieldMissing ->
--                                 CheckErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeVariant fields))
--             _ ->
--                 let res = bindPattern env pat (TypeVariant fields) >>= \env' -> exprCheck env' expr tyC
--                     allTrue = Map.map (const True) seenMap
--                 in res >>> go rest allTrue

-- checkMatchCasesBool :: Env -> [MatchCase] -> Type -> CheckResult
-- checkMatchCasesBool env cases tyC =
--     go cases False False
--   where
--     go [] seenTrue seenFalse
--       | not seenTrue  = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases)
--       | not seenFalse = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases)
--       | otherwise     = CheckOk

--     go (AMatchCase pat expr : rest) seenTrue seenFalse =
--       case pat of
--         PatternTrue  ->
--             exprCheck env expr tyC >>> go rest True seenFalse
--         PatternFalse ->
--             exprCheck env expr tyC >>> go rest seenTrue True
--         _ ->
--             let res = bindPattern env pat TypeBool >>= \env' -> exprCheck env' expr tyC
--             in res >>> go rest True True

-- checkMatchCasesNat :: Env -> [MatchCase] -> Type -> CheckResult
-- checkMatchCasesNat env cases tyC =
--     go cases False False
--   where
--     go [] seenZero seenSucc
--       | not seenZero  = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases)
--       | not seenSucc = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases)
--       | otherwise     = CheckOk

--     go (AMatchCase pat expr : rest) seenZero seenSucc =
--       case pat of
--         PatternInt 0  ->
--             exprCheck env expr tyC >>> go rest True seenSucc
--         PatternSucc(PatternInt 0) ->
--             exprCheck env expr tyC >>> go rest seenZero seenSucc
--         PatternSucc(PatternVar a) ->
--             let res = bindPattern env (PatternVar a) TypeNat >>= \env' -> exprCheck env' expr tyC
--             in res >>> go rest seenZero True
--         PatternVar a ->
--             let res = bindPattern env pat TypeBool >>= \env' -> exprCheck env' expr tyC
--             in res >>> go rest True True
--         _ ->
--             let res = bindPattern env pat TypeBool >>= \env' -> exprCheck env' expr tyC
--             in res >>> go rest False False

checkMatchCasesGeneric :: Env -> [MatchCase] -> Type -> Type -> CheckResult
checkMatchCasesGeneric env cases ty tyC =
    go cases
  where
    go [] = CheckOk emptyUEqs
    go (AMatchCase pat expr : rest) = do
        env' <- bindPattern env pat ty
        c1   <- exprCheck env' expr tyC
        c2   <- go rest
        return (c1 <> c2)


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
                CheckOk ueqs -> --TODO
                    InferOk tyC

-- Helpers
checkParams :: Env -> [ParamDecl] -> [Type] -> (CheckResult, Env)
checkParams env [] [] = (CheckOk emptyUEqs, env)
checkParams env (AParamDecl ident actualTy : ps) (ty : tys)
    | length ps /= length tys =
        (CheckErr ERROR_UNEXPECTED_NUMBER_OF_PARAMETERS_IN_LAMBDA, env)
    -- Если ожидаемый тип — переменная типа
    | TypeVar varIdent <- ty =
        let eqsThis = unify ty actualTy
            newEnv  = env { envVars = (ident, actualTy) : envVars env }
        in case checkParams newEnv ps tys of
             (CheckOk eqsRest, env') -> (CheckOk (eqsThis <> eqsRest), env')
             (CheckErr err, _)       -> (CheckErr err, env)
    | TypeVar varIdent <- actualTy =
        let eqsThis = unify ty actualTy
            newEnv  = env { envVars = (ident, actualTy) : envVars env }
        in case checkParams newEnv ps tys of
             (CheckOk eqsRest, env') -> (CheckOk (eqsThis <> eqsRest), env')
             (CheckErr err, _)       -> (CheckErr err, env)
    -- Если обычный тип и он <: фактический тип параметра
    | (<:=) env ty actualTy =
        let newEnv = env { envVars = (ident, ty) : envVars env }
        in case checkParams newEnv ps tys of
             (CheckOk eqsRest, env') -> (CheckOk eqsRest, env')
             (CheckErr err, _)       -> (CheckErr (ERROR_UNEXPECTED_TYPE_FOR_PARAMETER ident ty actualTy), env)
    | otherwise =
        (CheckErr (ERROR_UNEXPECTED_TYPE_FOR_PARAMETER ident ty actualTy), env)
checkParams env _ _ = (CheckErr ERROR_UNEXPECTED_NUMBER_OF_PARAMETERS_IN_LAMBDA, env)


checkArgs :: Env -> [Expr] -> [Type] -> CheckResult
checkArgs _   []     []       = CheckOk emptyUEqs
checkArgs env (e:es) (ty:tys)
    | length es /= length tys = CheckErr ERROR_INCORRECT_NUMBER_OF_ARGUMENTS
    | otherwise = (exprCheck env e ty) <> (checkArgs env es tys)

updateEnvByParams :: Env -> [ParamDecl] -> Env
updateEnvByParams env params =
    env { envVars = envVars env ++ [(ident, t) | AParamDecl ident t <- params] }