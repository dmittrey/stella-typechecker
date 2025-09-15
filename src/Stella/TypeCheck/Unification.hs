module Stella.TypeCheck.Unification where

import Stella.Abs

import Data.Traversable (mapAccumL)

-- Типы ошибок при проверке типов
data CErrType
    -- Собственные ошибки
    = ERROR_DECL_CHECK_NOT_IMPLEMENTED Decl
    | ERROR_EXPR_CHECK_NOT_IMPLEMENTED Expr Type
    | ERROR_EXPR_INFER_NOT_IMPLEMENTED Expr
    | ERROR_PATTERN_NOT_SUPPORTED Pattern Type
    | ERROR_MATCH_NOT_SUPPORTED Type
    | MONAD_FAIL_NOT_GUARDED_IM_BEGINNING_SORRY

    -- Требуемые ошибки
    | ERROR_AMBIGUOUS_PATTERN_TYPE Pattern
    | ERROR_MISSING_MAIN
    | ERROR_UNDEFINED_VARIABLE StellaIdent
    | ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION Type Type -- Expected Got
    | ERROR_NOT_A_FUNCTION Expr
    | ERROR_NOT_A_TUPLE Expr
    | ERROR_NOT_A_RECORD Expr
    | ERROR_UNEXPECTED_LAMBDA Expr
    | ERROR_UNEXPECTED_TYPE_FOR_PARAMETER StellaIdent Type Type -- Ident Expected Got
    | ERROR_UNEXPECTED_TUPLE Expr Type
    | ERROR_UNEXPECTED_RECORD Expr Type
    | ERROR_UNEXPECTED_VARIANT
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
    | ERROR_AMBIGUOUS_LIST_TYPE
    | ERROR_NOT_A_LIST Type
    | ERROR_ILLEGAL_EMPTY_MATCHING
    | ERROR_NONEXHAUSTIVE_MATCH_PATTERNS [MatchCase]
    | ERROR_UNEXPECTED_PATTERN_FOR_TYPE Type
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
    | ERROR_NOT_A_REFERENCE Expr
    | ERROR_UNEXPECTED_MEMORY_ADDRESS String
    | ERROR_AMBIGUOUS_REFERENCE_TYPE
    | ERROR_AMBIGUOUS_PANIC_TYPE
    | ERROR_EXCEPTION_TYPE_NOT_DECLARED Expr
    | ERROR_AMBIGUOUS_THROW_TYPE
    | ERROR_UNEXPECTED_SUBTYPE Type Type -- SubType Type
    | ERROR_UNEXPECTED_REFERENCE
    | ERROR_OCCURS_CHECK_INFINITE_TYPE
    | DEBUG Type Type
    | DEBUGG Expr
  deriving (Eq, Ord, Show, Read)

newtype Subs = Subs [(StellaIdent, Type)] deriving (Eq, Ord, Read)

instance Show Subs where
    show (Subs []) = "{}"   -- или "∅", или "empty substitution"
    show (Subs xs) = unlines (map showPair xs)
      where
        showPair (StellaIdent name, u) = name ++ " = " ++ show u

instance Semigroup Subs where
    (Subs a) <> (Subs b) = Subs (a ++ b)

type UEq = (Type, Type)

type UEqs = [UEq]

unify :: Type -> Type -> UEqs
unify t1 t2 = [(t1, t2)]

emptyUEqs :: UEqs
emptyUEqs = []

inFreeVars :: StellaIdent -> Type -> Bool
inFreeVars ident (TypeVar varIdent) =
    ident == varIdent
inFreeVars ident (TypeFun params ret) =
    any (inFreeVars ident) params || inFreeVars ident ret
inFreeVars _ _ =
    False


subsUnif :: Type -> -- In which term
            StellaIdent -> -- What we subs
            Type -> -- On what we subs
            Type -- Result
-- If varIdent match => we subs
subsUnif pre@(TypeVar varIdent) ident replaceType
    | varIdent == ident = replaceType
    | otherwise         = pre
-- No changes
subsUnif pre ident replaceUnif = pre

subsEq :: StellaIdent -> -- Which var we subs
            Type -> -- On what we subs
            UEq -> 
            UEq
subsEq ident replaceUnif (lu, ru) =
    ((subsUnif lu ident replaceUnif), (subsUnif ru ident replaceUnif))

unifSolve :: [UEq] -> Either CErrType Subs
-- C is emptyList => []
unifSolve [] = do
    return (Subs [])

-- trivial: same variable on both sides X = X
unifSolve ((TypeVar x, TypeVar y) : xs)
    | x == y    = unifSolve xs

-- S is UnifVar X && if X not in FV(T) => unify([X -> T]C') ∘ [X -> T]
unifSolve (((TypeVar x), t) : xs)
    | inFreeVars x t  = Left ERROR_OCCURS_CHECK_INFINITE_TYPE
    | otherwise       = do
        (Subs unifToType) <- unifSolve (map (subsEq x t) xs)
        return (Subs (unifToType ++ [(x, t)]))

-- T is UnifVar X && if X not in FV(S) => unify([X -> S]C') ∘ [X -> S]
unifSolve ((s, (TypeVar x)) : xs)
    | inFreeVars x s  = Left ERROR_OCCURS_CHECK_INFINITE_TYPE
    | otherwise       = do
        (Subs unifToType) <- unifSolve (map (subsEq x s) xs)
        return (Subs (unifToType ++ [(x, s)]))

-- S is UnifArrow S1 -> S2 && T is UnifArrow T1 -> T2 => unify(C' ∪ {S1 = T1} ∪ {S2 = T2})
unifSolve ((TypeFun sParams sRet, TypeFun tParams tRet) : xs)
    | length sParams /= length tParams = Left ERROR_INCORRECT_NUMBER_OF_ARGUMENTS
    | otherwise =
        let paramEqs = zipWith (\s t -> (s, t)) sParams tParams
            newEqs = paramEqs ++ [(sRet, tRet)]
        in unifSolve (xs ++ newEqs)

-- S = List S1 && T = List T1 => unify(S1 = T1)
unifSolve ((TypeList sElem, TypeList tElem) : xs) =
    unifSolve ((sElem, tElem) : xs)

-- S = T => unify C'
unifSolve ((sTy, tTy) : xs)
    | sTy /= tTy = Left (DEBUG sTy tTy)
    | otherwise  = unifSolve xs

-- | Генерация новых переменных для TypeAuto
type LastBusyIdx = Integer

freshVar :: LastBusyIdx -> (LastBusyIdx, Type)
freshVar lastIdx =
    let idx = lastIdx + 1
        newVar = TypeVar (StellaIdent ("T" ++ show idx))
    in (idx, newVar)

-- | Основная рекурсивная замена TypeAuto во всех типах
freshType :: LastBusyIdx -> Type -> (LastBusyIdx, Type)
freshType lastIdx TypeAuto = freshVar lastIdx
freshType lastIdx (TypeFun args ret) =
    let (last', args') = mapAccumL freshType lastIdx args
        (last'', ret') = freshType last' ret
    in (last'', TypeFun args' ret')
freshType lastIdx (TypeForAll vars ty) =
    let (last', ty') = freshType lastIdx ty
    in (last', TypeForAll vars ty')
freshType lastIdx (TypeRec ident ty) =
    let (last', ty') = freshType lastIdx ty
    in (last', TypeRec ident ty')
freshType lastIdx (TypeSum t1 t2) =
    let (last', t1') = freshType lastIdx t1
        (last'', t2') = freshType last' t2
    in (last'', TypeSum t1' t2')
freshType lastIdx (TypeTuple tys) =
    let (last', tys') = mapAccumL freshType lastIdx tys
    in (last', TypeTuple tys')
freshType lastIdx (TypeList ty) =
    let (last', ty') = freshType lastIdx ty
    in (last', TypeList ty')
freshType lastIdx (TypeRef ty) =
    let (last', ty') = freshType lastIdx ty
    in (last', TypeRef ty')
freshType lastIdx (TypeRecord fields) =
    let (last', fields') = mapAccumL freshRecordField lastIdx fields
    in (last', TypeRecord fields')
freshType lastIdx (TypeVariant fields) =
    let (last', fields') = mapAccumL freshVariantField lastIdx fields
    in (last', TypeVariant fields')
freshType lastIdx ty@(TypeBool)   = (lastIdx, ty)
freshType lastIdx ty@(TypeNat)    = (lastIdx, ty)
freshType lastIdx ty@(TypeUnit)   = (lastIdx, ty)
freshType lastIdx ty@(TypeTop)    = (lastIdx, ty)
freshType lastIdx ty@(TypeBottom) = (lastIdx, ty)
freshType lastIdx ty@(TypeVar _)  = (lastIdx, ty)

-- | Обновление полей record
freshRecordField :: LastBusyIdx -> RecordFieldType -> (LastBusyIdx, RecordFieldType)
freshRecordField lastIdx (ARecordFieldType name ty) =
    let (last', ty') = freshType lastIdx ty
    in (last', ARecordFieldType name ty')

-- | Обновление полей variant
freshVariantField :: LastBusyIdx -> VariantFieldType -> (LastBusyIdx, VariantFieldType)
freshVariantField lastIdx (AVariantFieldType name ty) =
    let (last', ty') = freshOptionalTyping lastIdx ty
    in (last', AVariantFieldType name ty')

-- | OptionalTyping (например SomeTyping TypeAuto)
freshOptionalTyping :: LastBusyIdx -> OptionalTyping -> (LastBusyIdx, OptionalTyping)
freshOptionalTyping lastIdx (SomeTyping TypeAuto) =
    let (a, b) = freshVar lastIdx
    in (a, SomeTyping b)
freshOptionalTyping lastIdx ty = (lastIdx, ty)

-- | Рекурсивная обработка параметров
freshParamDecl :: LastBusyIdx -> ParamDecl -> (LastBusyIdx, ParamDecl)
freshParamDecl lastIdx (AParamDecl ident ty) =
    let (last', ty') = freshType lastIdx ty
    in (last', AParamDecl ident ty')

-- | Рекурсивная обработка Expr
freshExpr :: LastBusyIdx -> Expr -> (LastBusyIdx, Expr)
freshExpr lastIdx expr = case expr of
    Abstraction params body ->
        let (last', uParams) = mapAccumL freshParamDecl lastIdx params
            (last'', uBody)   = freshExpr last' body
        in (last'', Abstraction uParams uBody)
    Let bindings body ->
        let (last', uBindings) = mapAccumL freshPatternBinding lastIdx bindings
            (last'', uBody)     = freshExpr last' body
        in (last'', Let uBindings uBody)
    LetRec bindings body ->
        let (last', uBindings) = mapAccumL freshPatternBinding lastIdx bindings
            (last'', uBody)     = freshExpr last' body
        in (last'', LetRec uBindings uBody)
    NatRec e1 e2 fnBody ->
        let (last', uE1)   = freshExpr lastIdx e1
            (last'', uE2)  = freshExpr last' e2
            (last''', uFn) = freshExpr last'' fnBody
        in (last''', NatRec uE1 uE2 uFn)
    Application f args ->
        let (last', uF)     = freshExpr lastIdx f
            (last'', uArgs) = mapAccumL freshExpr last' args
        in (last'', Application uF uArgs)
    Tuple exprs ->
        let (last', uExprs) = mapAccumL freshExpr lastIdx exprs
        in (last', Tuple uExprs)
    Record bindings ->
        let (last', uBindings) = mapAccumL freshBinding lastIdx bindings
        in (last', Record uBindings)
    List exprs ->
        let (last', uExprs) = mapAccumL freshExpr lastIdx exprs
        in (last', List uExprs)
    ConsList e1 e2 ->
        let (last', uE1)  = freshExpr lastIdx e1
            (last'', uE2) = freshExpr last' e2
        in (last'', ConsList uE1 uE2)
    Inl e ->
        let (last', uE) = freshExpr lastIdx e
        in (last', Inl uE)
    Inr e ->
        let (last', uE) = freshExpr lastIdx e
        in (last', Inr uE)
    Succ e ->
        let (last', uE) = freshExpr lastIdx e
        in (last', Succ uE)
    Pred e ->
        let (last', uE) = freshExpr lastIdx e
        in (last', Pred uE)
    Head e ->
        let (last', uE) = freshExpr lastIdx e
        in (last', Head uE)
    Tail e ->
        let (last', uE) = freshExpr lastIdx e
        in (last', Tail uE)
    IsEmpty e ->
        let (last', uE) = freshExpr lastIdx e
        in (last', IsEmpty uE)
    Fix e ->
        let (last', uE) = freshExpr lastIdx e
        in (last', Fix uE)
    DotTuple e idx ->
        let (last', uE) = freshExpr lastIdx e
        in (last', DotTuple uE idx)
    DotRecord e ident ->
        let (last', uE) = freshExpr lastIdx e
        in (last', DotRecord uE ident)
    TypeAsc e ty ->
        let (last', uTy) = freshType lastIdx ty
            (last'', uE) = freshExpr last' e
        in (last'', TypeAsc uE uTy)
    TypeCast e ty ->
        let (last', uTy) = freshType lastIdx ty
            (last'', uE) = freshExpr last' e
        in (last'', TypeCast uE uTy)
    Variant ident exprData ->
        let (last', uExprData) = freshExprData lastIdx exprData
        in (last', Variant ident uExprData)
    _ -> (lastIdx, expr)

-- | Обработка PatternBinding
freshPatternBinding :: LastBusyIdx -> PatternBinding -> (LastBusyIdx, PatternBinding)
freshPatternBinding lastIdx (APatternBinding pat expr) =
    let (last', uExpr) = freshExpr lastIdx expr
        (last'', uPat) = freshPattern last' pat
    in (last'', APatternBinding uPat uExpr)

-- | Обработка Pattern
freshPattern :: LastBusyIdx -> Pattern -> (LastBusyIdx, Pattern)
freshPattern lastIdx pat = case pat of
    PatternVar ident -> (lastIdx, PatternVar ident)
    PatternInl p     -> let (last', uP) = freshPattern lastIdx p in (last', PatternInl uP)
    PatternInr p     -> let (last', uP) = freshPattern lastIdx p in (last', PatternInr uP)
    PatternTuple ps  -> let (last', uPs) = mapAccumL freshPattern lastIdx ps in (last', PatternTuple uPs)

-- freshPattern lastIdx (PatternRecord fields) =
--     let (last', uFields) = mapAccumL (\idx (name,p) -> let (idx', up) = freshPattern idx p in (idx', (name,up))) lastIdx fields
--     in (last', PatternRecord (map (uncurry LabelledPattern) uFields))

-- freshPattern lastIdx (PatternVariant ident maybeP) =
--     case maybeP of
--         Nothing -> (lastIdx, PatternVariant ident Nothing)
--         Just p  -> let (last', uP) = freshPattern lastIdx p
--                    in (last', PatternVariant ident (Just (PatternData uP)))

-- | ExprData внутри Variant
freshExprData :: LastBusyIdx -> ExprData -> (LastBusyIdx, ExprData)
freshExprData lastIdx exprData = case exprData of
    NoExprData     -> (lastIdx, NoExprData)
    SomeExprData e -> let (last', uE) = freshExpr lastIdx e in (last', SomeExprData uE)

-- | Binding в Record
freshBinding :: LastBusyIdx -> Binding -> (LastBusyIdx, Binding)
freshBinding lastIdx (ABinding name expr) =
    let (last', uExpr) = freshExpr lastIdx expr
    in (last', ABinding name uExpr)

-- | Обновление тела функции и всех типов
freshDecl :: LastBusyIdx -> Decl -> (LastBusyIdx, Decl)
freshDecl lastIdx (DeclFun anns ident params retTy throwTy decls body) =
    let (last', uDecls)  = mapAccumL freshDecl lastIdx decls
        (last'', uParams) = mapAccumL freshParamDecl last' params
        (last''', uRetTy) = freshReturnType last'' retTy
        (last'''', uBody)  = freshExpr last''' body
    in (last'''', DeclFun anns ident uParams uRetTy throwTy uDecls uBody)
freshDecl lastIdx decl = (lastIdx, decl)

freshReturnType :: LastBusyIdx -> ReturnType -> (LastBusyIdx, ReturnType)
freshReturnType lastIdx NoReturnType = (lastIdx, NoReturnType)
freshReturnType lastIdx (SomeReturnType ty) =
    let (last', ty') = freshType lastIdx ty
    in (last', SomeReturnType ty')

-- | Основная функция по программе
freshProgram :: LastBusyIdx -> Program -> Program
freshProgram lastIdx (AProgram a1 a2 decls) =
    let (_, uDecls) = mapAccumL freshDecl lastIdx decls
    in AProgram a1 a2 uDecls
