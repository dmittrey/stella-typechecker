module Stella.TypeCheck.Unification where

import Stella.Abs

import Data.Traversable (mapAccumL)

newtype Subs = Subs [(StellaIdent, Unif)] deriving (Eq, Ord, Read)

instance Show Subs where
    show (Subs []) = "{}"   -- или "∅", или "empty substitution"
    show (Subs xs) = unlines (map showPair xs)
      where
        showPair (StellaIdent name, u) = name ++ " = " ++ show u

instance Semigroup Subs where
    (Subs a) <> (Subs b) = Subs (a ++ b)

data Unif
    = UType    Type
    | UVar     StellaIdent
    | UArrow   Unif Unif
  deriving (Eq, Ord, Read)

instance Show Unif where
    show (UType ty) = show ty
    show (UVar (StellaIdent name)) = name
    show (UArrow u1 u2) = "(" ++ show u1 ++ " -> " ++ show u2 ++ ")"

data UnifErr
    = ERROR_OCCURS_CHECK_INFINITE_TYPE
    | ERROR_UNIF_NOT_EQUALS_TYPES Type Type
    | ERROR_UNIF_FAIL
  deriving (Eq, Ord, Show, Read)

newtype UnifEq = UEq (Unif, Unif) deriving (Eq, Ord, Read)

instance Show UnifEq where
    show (UEq (a1, a2)) = show a1 ++ " = " ++ show a2

newtype UnifEqs = UnifEqs [UnifEq] deriving (Eq, Ord, Read)

instance Show UnifEqs where
    show (UnifEqs []) = "{}"
    show (UnifEqs xs) = unlines (map showPair xs)
      where
        showPair (UEq (a1, a2)) = show a1 ++ " = " ++ show a2

instance Semigroup UnifEqs where
    (UnifEqs a) <> (UnifEqs b) = UnifEqs (a ++ b)

unify :: Unif -> Type -> UnifEqs
unify u ty = UnifEqs [UEq (u, UType ty)]

unifyEq :: Unif -> Unif -> UnifEqs
unifyEq u1 u2 = UnifEqs [UEq (u1, u2)]

emptyUEqs :: UnifEqs
emptyUEqs = UnifEqs []

inFreeVars :: StellaIdent -> Unif -> Bool
inFreeVars ident (UType _) =
    False
inFreeVars ident (UVar varIdent) =
    ident == varIdent
inFreeVars ident (UArrow lu ru) =
    inFreeVars ident lu || inFreeVars ident ru

subsUnif :: Unif -> -- In which term
            StellaIdent -> -- What we subs
            Unif -> -- On what we subs
            Unif -- Result
-- No changes
subsUnif pre@(UType _) ident replaceUnif = pre
-- If varIdent match => we subs
subsUnif pre@(UVar varIdent) ident replaceUnif
    | varIdent == ident = replaceUnif
    | otherwise         = pre
-- Recursive collect replaces UnifArrow
subsUnif (UArrow lu ru) ident replaceUnif =
    (UArrow (subsUnif lu ident replaceUnif) (subsUnif ru ident replaceUnif))

subsEq :: StellaIdent -> -- Which var we subs
            Unif -> -- On what we subs
            UnifEq -> 
            UnifEq
subsEq ident replaceUnif (UEq (lu, ru)) =
    UEq ((subsUnif lu ident replaceUnif), (subsUnif ru ident replaceUnif))

unifSolve :: [UnifEq] -> Either UnifErr Subs
-- C is emptyList => []
unifSolve [] = do
    return (Subs [])

-- S = T => unify C'
unifSolve (UEq ((UType sTy), (UType tTy)) : xs)
    | sTy /= tTy = Left (ERROR_UNIF_NOT_EQUALS_TYPES sTy tTy)
    | otherwise  = unifSolve xs

-- trivial: same variable on both sides X = X
unifSolve (UEq (UVar x, UVar y) : xs)
    | x == y    = unifSolve xs

-- S is UnifVar X && if X not in FV(T) => unify([X -> T]C') ∘ [X -> T]
unifSolve (UEq ((UVar x), t) : xs)
    | inFreeVars x t  = Left ERROR_OCCURS_CHECK_INFINITE_TYPE
    | otherwise       = do
        (Subs unifToType) <- unifSolve (map (subsEq x t) xs)
        return (Subs (unifToType ++ [(x, t)]))

-- T is UnifVar X && if X not in FV(S) => unify([X -> S]C') ∘ [X -> S]
unifSolve (UEq (s, (UVar x)) : xs)
    | inFreeVars x s  = Left ERROR_OCCURS_CHECK_INFINITE_TYPE
    | otherwise       = do
        (Subs unifToType) <- unifSolve (map (subsEq x s) xs)
        return (Subs (unifToType ++ [(x, s)]))

-- S is UnifArrow S1 -> S2 && T is UnifArrow T1 -> T2 => unify(C' ∪ {S1 = T1} ∪ {S2 = T2})
unifSolve (UEq ((UArrow s1 s2), (UArrow t1 t2)) : xs) =
    unifSolve (xs ++ [UEq (s1, t1), UEq (s2, t2)])

-- else FAIL
unifSolve _ = Left ERROR_UNIF_FAIL

type LastBusyIdx = Integer

freshVar :: LastBusyIdx -> (LastBusyIdx, Unif)
freshVar lastIdx =
    let idx = lastIdx + 1
        newVar = UVar (StellaIdent ("T" ++ show idx))
    in (idx, newVar)

freshTy :: LastBusyIdx -> Type -> (LastBusyIdx, Unif)
freshTy lastIdx TypeAuto        = freshVar lastIdx
freshTy lastIdx (TypeVar ident) = (lastIdx, UVar ident) -- Not generate new name if ident is exist
freshTy lastIdx ty              = (lastIdx, UType ty)

data UProgram = UProgram LanguageDecl [Extension] [UDecl]
  deriving (Eq, Ord, Show, Read)

freshProgram :: LastBusyIdx -> Program -> UProgram
freshProgram lastIdx (AProgram a1 a2 decls) =
    let (_, uDecls) = mapAccumL freshDecl lastIdx decls
    in UProgram a1 a2 uDecls

data UDecl
    = UDeclFun [Annotation] StellaIdent [UParamDecl] UReturnType ThrowType [UDecl] Expr
    -- TODO
    -- | UDeclFunGeneric [Annotation] StellaIdent [StellaIdent] [UParamDecl] UReturnType ThrowType [UDecl] Expr
    -- | UDeclTypeAlias StellaIdent Type
    | UDeclExceptionType Type                -- No need to reconstruct types for exceptions
    | UDeclExceptionVariant StellaIdent Type -- Also
    deriving (Eq, Ord, Show, Read)

freshDecl :: LastBusyIdx -> Decl -> (LastBusyIdx, UDecl)
freshDecl lastIdx (DeclFun anns funIdent params retTy throwTy decls expr) =
    let (newLastIdx,  uDecls) = mapAccumL freshDecl       lastIdx  decls
        (newLastIdx1, uParams) = mapAccumL freshParamDecl newLastIdx params
        (newLastIdx2, uRetTy)  = freshReturnType newLastIdx1 retTy
    in 
        (newLastIdx2, UDeclFun anns funIdent uParams uRetTy throwTy uDecls expr)

data UParamDecl = UParamDecl StellaIdent Unif
  deriving (Eq, Ord, Show, Read)

freshParamDecl :: LastBusyIdx -> ParamDecl -> (LastBusyIdx, UParamDecl)
freshParamDecl lastIdx (AParamDecl ident ty) =
    let (newLastIdx, unifTy) = freshTy lastIdx ty
    in (newLastIdx, UParamDecl ident unifTy)

data UReturnType = UNoReturnType | USomeReturnType Unif
    deriving (Eq, Ord, Show, Read)

freshReturnType :: LastBusyIdx -> ReturnType -> (LastBusyIdx, UReturnType)
freshReturnType lastIdx NoReturnType = (lastIdx, UNoReturnType)
freshReturnType lastIdx (SomeReturnType ty) =
    let (newLastIdx, unifTy) = freshTy lastIdx ty
    in (newLastIdx, USomeReturnType unifTy)
