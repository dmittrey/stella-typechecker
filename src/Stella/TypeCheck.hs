{-# LANGUAGE PatternSynonyms #-}

module Stella.TypeCheck where

import Stella.Abs
import Stella.ErrM

import Data.Maybe
import Data.List
import Prelude

-- TODO

-- Record
-- TypeSum
-- Lists
-- Variant
-- Fixed point

-- Let errors
-- 8. Организовать тестовое покрытие(переназвать файлы, пройтись по кейсам)

data MissingMatchCase
    = MissingInr
    | MissingInl
  deriving (Eq, Ord, Show, Read)

-- Типы ошибок
data CErrType
    = C_ERROR_EXPR_NOT_IMPLEMENTED_YET Expr Type
    | C_ERROR_DECL_NOT_IMPLEMENTED_YET Decl
    | I_ERROR_EXPR_NOT_IMPLEMENTED_YET Expr
    | ERROR_Unknown_ident_for_binding [Expr] [Type]
    -- | C_ERROR_EXPR_NOT_IMPLEMENTED_YET_I [MatchCase]
    -- | I_ERROR_EXPR_NOT_IMPLEMENTED_YET_I Pattern
    -- | I_ERROR_EXPR_NOT_IMPLEMENTED_YET_I_I [MatchCase]

    | ERROR_MISSING_MAIN
    | ERROR_UNDEFINED_VARIABLE StellaIdent
    | ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_S
    | ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION Expr Type Type -- Expr Expected Got
    | ERROR_NOT_A_FUNCTION Expr
    | ERROR_NOT_A_TUPLE Expr
    -- | ERROR_NOT_A_RECORD Expr
    | ERROR_UNEXPECTED_LAMBDA Expr Type
    | ERROR_UNEXPECTED_TYPE_FOR_PARAMETER StellaIdent Type Type -- Ident Expected Got
    | ERROR_UNEXPECTED_TUPLE Expr Type
    -- | ERROR_UNEXPECTED_RECORD Expr Type
    -- | ERROR_UNEXPECTED_VARIANT Expr
    -- ERROR_UNEXPECTED_LIST
    -- | ERROR_UNEXPECTED_INJECTION Expr
    -- ERROR_UNEXPECTED_RECORD_FIELDS
    -- | ERROR_UNEXPECTED_FIELD_ACCESS Expr StellaIdent
    -- | ERROR_UNEXPECTED_VARIANT_LABEL
    | ERROR_TUPLE_INDEX_OUT_OF_BOUNDS Expr Integer
    | ERROR_UNEXPECTED_TUPLE_LENGTH
    -- | ERROR_AMBIGUOUS_SUM_TYPE Expr
    -- | ERROR_AMBIGUOUS_VARIANT_TYPE
    -- ERROR_AMBIGUOUS_LIST
    -- | ERROR_ILLEGAL_EMPTY_MATCHING
    -- | ERROR_NONEXHAUSTIVE_MATCH_PATTERNS [MatchCase] MissingMatchCase
    -- | ERROR_UNEXPECTED_PATTERN_FOR_TYPE Pattern Type
    -- ERROR_DUPLICATE_RECORD_FIELDS
    -- ERROR_DUPLICATE_RECORD_TYPE_FIELDS
    -- ERROR_DUPLICATE_VARIANT_TYPE_FIELDS
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
checkArgs _   []     _      = CheckErr ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_S
checkArgs _   _      []     = CheckErr ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_S
checkArgs env (e:es) (ty:tys) =
  exprCheck env e ty
  >>> checkArgs env es tys

declCheck :: Env -> Decl -> (CheckResult, Env)
declCheck env (DeclFun _ name [] NoReturnType _ _ expr) =
    (exprCheck env expr TypeUnit, env)
declCheck env (DeclFun _ name [] (SomeReturnType retTy) _ _ expr) =
    (exprCheck env expr retTy, env)
declCheck env (DeclFun anns name paramsAnn retTy throwTy decls expr) =
    let env'        = updateEnvByParams env paramsAnn
        resultTy    = case retTy of
                        NoReturnType      -> TypeUnit
                        SomeReturnType ty -> ty
        funTy       = TypeFun [t | AParamDecl _ t <- paramsAnn] resultTy
        (checkRes, innerEnv) =
            declCheck env' (DeclFun anns name [] retTy throwTy decls expr)
    in (checkRes, innerEnv ++ [(name, funTy)])

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
    checkParams env [] _  = (CheckErr ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_S, env)
    checkParams env _  [] = (CheckErr ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_S, env)
    checkParams env ((AParamDecl ident actualTy):ps) (ty:tys)
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

-- -- ====== T-Record ======
-- exprCheck env (Record []) (TypeRecord []) =
--     CheckOk

-- exprCheck env (Record _) (TypeRecord []) =
--     CheckErr ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_SILENT

-- exprCheck env (Record []) (TypeRecord _) =
--     CheckErr ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION_SILENT

-- exprCheck env record_e@(Record (ABinding ident e : es)) (TypeRecord (ARecordFieldType l ty : flds)) 
--     | ident /= l = CheckErr (ERROR_UNEXPECTED_FIELD_ACCESS record_e ident)   -- порядок/имена не совпали
--     | otherwise  =
--         exprCheck env e ty
--         >>> exprCheck env (Record es) (TypeRecord flds)

-- exprCheck env expression@(Record _) ty =
--     CheckErr (ERROR_UNEXPECTED_RECORD expression ty)

-- -- ====== T-RecordProj ======
-- -- t.l_j : T_j
-- exprCheck env (DotRecord expr ident) ty =
--     case exprInfer env (DotRecord expr ident) of
--         InferOk actualTy ->
--             if ty == actualTy
--             then CheckOk
--             else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION (DotRecord expr ident) ty actualTy)
--         InferErr err ->
--             CheckErr err

-- -- ====== T-Inl ======
-- exprCheck env (Inl expr) (TypeSum t1 t2) = exprCheck env expr t1

-- exprCheck env (Inl expr) _ = CheckErr (ERROR_UNEXPECTED_INJECTION expr)

-- -- ====== T-Inr ======
-- exprCheck env (Inr expr) (TypeSum t1 t2) = exprCheck env expr t2

-- exprCheck env (Inr expr) _ = CheckErr (ERROR_UNEXPECTED_INJECTION expr)

-- -- ====== T-Case ======
-- exprCheck env (Match t1 cases) tyC =
--     case exprInfer env t1 of
--         InferErr err ->
--             CheckErr err
--         InferOk ty1 ->
--             checkMatchCases env cases ty1 tyC

-- -- ====== T-Variant ======
-- exprCheck env (Variant ident exprData) (TypeVariant fields) =
--     let identToType = [(ident, t) | AVariantFieldType ident t <- fields]
--     in case lookup ident identToType of
--         Just t -> CheckOk
--         Nothing -> CheckErr ERROR_UNEXPECTED_VARIANT_LABEL

-- exprCheck env expr@(Variant ident exprData) _ = CheckErr (ERROR_UNEXPECTED_VARIANT expr)

-- ====== Other ======

-- T-Equal
exprCheck env (Equal e1 e2) t =
    case exprInfer env e1 of
        InferOk ty1 ->
            exprCheck env e2 ty1
        InferErr err ->
            CheckErr err

exprCheck _ e t = CheckErr (C_ERROR_EXPR_NOT_IMPLEMENTED_YET e t)

-- checkMatchCases :: Env -> [MatchCase] -> Type -> Type -> CheckResult
-- --                Env |  Match Cases  | t1 type | C type
-- checkMatchCases env [] _ _ = CheckErr ERROR_ILLEGAL_EMPTY_MATCHING
-- checkMatchCases env [(AMatchCase (PatternInl pl) el), (AMatchCase (PatternInr pr) er)] (TypeSum t1 t2) ty =
--     case bindPattern env pl t1 of
--         InferErr err ->
--             InferErr err
--         InferOk envl ->
--             exprCheck envl el ty >>>
--             (case bindPattern env pr t2 of
--                 InferErr err ->
--                     InferErr err
--                 InferOk envr ->
--                     exprCheck envr er ty)
-- checkMatchCases _ cases@[(AMatchCase (PatternInl _) _), (AMatchCase _ _)] (TypeSum _ _) ty = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases MissingInr)
-- checkMatchCases _ cases@[(AMatchCase _ _), (AMatchCase (PatternInr _) _)] (TypeSum _ _) ty = CheckErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases MissingInl)

-- checkMatchCases env cases t1@(TypeVariant fields) tyC =
--     foldl (>>>) CheckOk (map checkOne cases)
--   where
--     checkOne :: MatchCase -> CheckResult
--     checkOne (AMatchCase p expr) =
--         case bindPattern env p t1 of
--             InferOk newEnv -> exprCheck newEnv expr tyC
--             InferErr err   -> CheckErr err




-- checkMatchCases _ cases _ _ = CheckErr (C_ERROR_EXPR_NOT_IMPLEMENTED_YET_I cases)

-- inferMatchCases :: Env -> [MatchCase] -> Type -> InferResult Type
-- --                Env |  Match Cases  | t1 type 
-- inferMatchCases env [] _ = InferErr ERROR_ILLEGAL_EMPTY_MATCHING
-- inferMatchCases env [(AMatchCase (PatternInl pl) e2), (AMatchCase (PatternInr pr) e3)] (TypeSum ty2 ty3) =
--     case bindPattern env pl ty2 of
--         InferErr err ->
--             InferErr err
--         InferOk env2 ->
--             case exprInfer env2 e2 of
--                 InferErr err ->
--                     InferErr err
--                 InferOk tyC ->
--                     case bindPattern env pr ty3 of
--                         InferErr err ->
--                             InferErr err
--                         InferOk env3 ->
--                             case exprCheck env3 e3 tyC of
--                                 CheckErr err ->
--                                     InferErr err
--                                 CheckOk ->
--                                     InferOk tyC
-- inferMatchCases _ cases@[(AMatchCase (PatternInl _) _), (AMatchCase _ _)] (TypeSum _ _) = InferErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases MissingInr)
-- inferMatchCases _ cases@[(AMatchCase _ _), (AMatchCase (PatternInr _) _)] (TypeSum _ _) = InferErr (ERROR_NONEXHAUSTIVE_MATCH_PATTERNS cases MissingInl)
-- inferMatchCases env cases t1@(TypeVariant fields) = 
--     foldl combine (InferOk TypeUnit) (map inferOne cases)
--   where
--     inferOne :: MatchCase -> InferResult Type
--     inferOne (AMatchCase p expr) =
--         case bindPattern env p t1 of
--             InferOk newEnv -> exprInfer newEnv expr
--             InferErr err   -> InferErr err

--     combine :: InferResult Type -> InferResult Type -> InferResult Type
--     combine (InferErr err) _ = InferErr err
--     combine _ (InferErr err) = InferErr err
--     combine (InferOk ty1) (InferOk ty2) =
--         if ty1 == TypeUnit then InferOk ty2
--         else if ty2 == TypeUnit then InferOk ty1
--         else if ty1 == ty2 then InferOk ty1
--         else InferErr (ERROR_AMBIGUOUS_VARIANT_TYPE)
-- inferMatchCases _ cases _ = InferErr (I_ERROR_EXPR_NOT_IMPLEMENTED_YET_I_I cases)

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

-- -- ====== T-Zero ======
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

-- -- ====== T-Record ======
-- exprInfer env (Record bindings) =
--         foldl step (InferOk (TypeRecord [])) bindings
--     where
--         step :: InferResult Type -> Binding -> InferResult Type
--         step (InferOk (TypeRecord acc)) (ABinding ident e) =
--             case exprInfer env e of
--                 InferOk ty ->
--                     InferOk (TypeRecord (acc ++ [(ARecordFieldType ident ty)]))
--                 InferErr err ->
--                     InferErr err

-- -- ====== T-RecordProj ======
-- exprInfer env (DotRecord expr ident) =
--     case exprInfer env expr of
--         InferOk (TypeRecord fields) ->
--             let identToType = [(ident, t) | ARecordFieldType ident t <- fields]
--             in case lookup ident identToType of
--                 Just ty  -> InferOk ty
--                 Nothing -> InferErr (ERROR_UNEXPECTED_FIELD_ACCESS expr ident)
--         InferOk otherTy ->
--             InferErr (ERROR_NOT_A_RECORD expr)
--         InferErr err ->
--             InferErr err

-- -- ====== T-Inl ======
-- exprInfer env (Inl expr) = InferErr (ERROR_AMBIGUOUS_SUM_TYPE expr)

-- -- ====== T-Inr ======
-- exprInfer env (Inr expr) = InferErr (ERROR_AMBIGUOUS_SUM_TYPE expr)

-- -- ====== T-Case ======
-- exprInfer env (Match t1 cases) =
--     case exprInfer env t1 of
--         InferErr err ->
--             InferErr err
--         InferOk ty1 ->
--             inferMatchCases env cases ty1

-- -- Other
exprInfer _ e = InferErr (I_ERROR_EXPR_NOT_IMPLEMENTED_YET e)

-- updateEnvByBindings :: Env -> [PatternBinding] -> InferResult Env
-- updateEnvByBindings env [] = Ok env
-- updateEnvByBindings env bindings =
--         foldl step (InferOk env) bindings
--     where
--         step :: InferResult Env -> PatternBinding -> InferResult Env
--         step (InferOk accEnv) (APatternBinding p e) =
--             case exprInfer accEnv e of
--                 InferErr err ->
--                     InferErr err
--                 InferOk ty ->
--                     bindPattern accEnv p ty

-- ====== HELPERS ======

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
bindPattern :: Env -> Pattern -> Type -> InferResult Env
bindPattern env (PatternVar ident) t =
    InferOk (env ++ [(ident, t)])

-- bindPattern env (PatternUnit) t =
    -- TODO
    -- InferOk env

-- bindPattern env (PatternInl p) (TypeSum t1 t2) =
--     bindPattern env p t1
-- bindPattern env p@(PatternInl pl) t =
--     InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE p t)

-- bindPattern env (PatternInr p) (TypeSum t1 t2) =
--     bindPattern env p t2
-- bindPattern env p@(PatternInr pr) t =
--     InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE p t)

-- bindPattern env (PatternVariant ident (SomePatternData p)) (TypeVariant fields) =
--     let identToType = [(ident, t) | AVariantFieldType ident t <- fields]
--     in case lookup ident identToType of
--         Just (NoTyping) ->
--             bindPattern env p TypeUnit
--         Just (SomeTyping ty) ->
--             bindPattern env p ty
--         Nothing -> 
--             InferErr ERROR_UNEXPECTED_VARIANT_LABEL
-- -- TODO find example
-- bindPattern env p@(PatternVariant ident (NoPatternData)) (TypeVariant fields) =
--     InferErr (I_ERROR_EXPR_NOT_IMPLEMENTED_YET_I p)
-- bindPattern env p@(PatternVariant ident pd) t =
--     InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE p t)
    

-- bindPattern env p _ = 
--     InferErr (I_ERROR_EXPR_NOT_IMPLEMENTED_YET_I p)