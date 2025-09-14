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
    | DEBUG Type
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

-- S = T => unify C'
unifSolve ((sTy, tTy) : xs)
    | sTy /= tTy = Left (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION sTy tTy)
    | otherwise  = unifSolve xs

type LastBusyIdx = Integer

freshVar :: LastBusyIdx -> (LastBusyIdx, Type)
freshVar lastIdx =
    let idx = lastIdx + 1
        newVar = TypeVar (StellaIdent ("T" ++ show idx))
    in (idx, newVar)

freshTy :: LastBusyIdx -> Type -> (LastBusyIdx, Type)
freshTy lastIdx TypeAuto        = freshVar lastIdx
freshTy lastIdx ty              = (lastIdx, ty)

type UProgram = Program

freshProgram :: LastBusyIdx -> Program -> UProgram
freshProgram lastIdx (AProgram a1 a2 decls) =
    let (_, uDecls) = mapAccumL freshDecl lastIdx decls
    in AProgram a1 a2 uDecls

type UDecl = Decl

freshDecl :: LastBusyIdx -> Decl -> (LastBusyIdx, UDecl)
freshDecl lastIdx (DeclFun anns funIdent params retTy throwTy decls expr) =
    let (newLastIdx,  uDecls) = mapAccumL freshDecl       lastIdx  decls
        (newLastIdx1, uParams) = mapAccumL freshParamDecl newLastIdx params
        (newLastIdx2, uRetTy)  = freshReturnType newLastIdx1 retTy
    in 
        (newLastIdx2, DeclFun anns funIdent uParams uRetTy throwTy uDecls expr)

type UParamDecl = ParamDecl

freshParamDecl :: LastBusyIdx -> ParamDecl -> (LastBusyIdx, UParamDecl)
freshParamDecl lastIdx (AParamDecl ident ty) =
    let (newLastIdx, unifTy) = freshTy lastIdx ty
    in (newLastIdx, AParamDecl ident unifTy)

type UReturnType = ReturnType

freshReturnType :: LastBusyIdx -> ReturnType -> (LastBusyIdx, UReturnType)
freshReturnType lastIdx NoReturnType =
    (lastIdx, NoReturnType)
freshReturnType lastIdx (SomeReturnType ty) =
    let (newLastIdx, unifTy) = freshTy lastIdx ty
    in (newLastIdx, SomeReturnType unifTy)
