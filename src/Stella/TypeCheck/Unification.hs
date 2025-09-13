module Stella.TypeCheck.Unification where

import Stella.Abs

newtype Subs = Subs [(StellaIdent, Unif)] deriving (Eq, Ord, Read)

instance Show Subs where
    show (Subs []) = "{}"   -- или "∅", или "empty substitution"
    show (Subs xs) = unlines (map showPair xs)
      where
        showPair (StellaIdent name, u) = name ++ " = " ++ show u

newtype UnifEq = UnifEq (Unif, Unif) deriving (Eq, Ord, Show, Read)

data UnifErr
    = ERROR_OCCURS_CHECK_INFINITE_TYPE
    | ERROR_UNIF_NOT_EQUALS_TYPES Type Type
    | ERROR_UNIF_FAIL
    | DEBUG StellaIdent Unif
  deriving (Eq, Ord, Show, Read)

data Unif
    = UnifType    Type
    | UnifVar     StellaIdent
    | UnifArrow   Unif Unif
  deriving (Eq, Ord, Read)

instance Show Unif where
    show (UnifType ty) = show ty
    show (UnifVar (StellaIdent name)) = name
    show (UnifArrow u1 u2) = "(" ++ show u1 ++ " -> " ++ show u2 ++ ")"


inFreeVars :: StellaIdent -> Unif -> Bool
inFreeVars ident (UnifType _) =
    False
inFreeVars ident (UnifVar varIdent) =
    ident == varIdent
inFreeVars ident (UnifArrow lUnif rUnif) =
    inFreeVars ident lUnif || inFreeVars ident rUnif


subsUnif :: Unif -> -- In which term
            StellaIdent -> -- What we subs
            Unif -> -- On what we subs
            Unif -- Result
-- No changes
subsUnif pre@(UnifType _) ident replaceUnif = pre
-- If varIdent match => we subs
subsUnif pre@(UnifVar varIdent) ident replaceUnif
    | varIdent == ident = replaceUnif
    | otherwise         = pre
-- Recursive collect replaces UnifArrow
subsUnif (UnifArrow lUnif rUnif) ident replaceUnif =
    (UnifArrow (subsUnif lUnif ident replaceUnif) (subsUnif rUnif ident replaceUnif))


unifSolve :: [UnifEq] -> Either UnifErr Subs
-- C is emptyList => []
unifSolve [] = do
    return (Subs [])

-- S = T => unify C'
unifSolve (UnifEq ((UnifType sTy), (UnifType tTy)) : xs)
    | sTy /= tTy = Left (ERROR_UNIF_NOT_EQUALS_TYPES sTy tTy)
    | otherwise  = unifSolve xs

-- trivial: same variable on both sides X = X
unifSolve (UnifEq (UnifVar x, UnifVar y) : xs)
    | x == y    = unifSolve xs

-- S is UnifVar X && if X not in FV(T) => unify([X -> T]C') ∘ [X -> T]
unifSolve (UnifEq ((UnifVar x), t) : xs)
    | inFreeVars x t  = Left ERROR_OCCURS_CHECK_INFINITE_TYPE
    | otherwise       = do
        (Subs unifToType) <- unifSolve (map (subsEq x t) xs)
        return (Subs (unifToType ++ [(x, t)]))
  where
    subsEq :: StellaIdent -> -- Which var we subs
            Unif -> -- On what we subs
            UnifEq -> 
            UnifEq
    subsEq ident replaceUnif (UnifEq (lUnif, rUnif)) =
        UnifEq ((subsUnif lUnif ident replaceUnif), (subsUnif rUnif ident replaceUnif))

-- T is UnifVar X && if X not in FV(S) => unify([X -> S]C') ∘ [X -> S]
unifSolve (UnifEq (s, (UnifVar x)) : xs)
    | inFreeVars x s  = Left ERROR_OCCURS_CHECK_INFINITE_TYPE
    | otherwise       = do
        (Subs unifToType) <- unifSolve (map (subsEq x s) xs)
        return (Subs (unifToType ++ [(x, s)]))
  where
    subsEq :: StellaIdent -> -- Which var we subs
            Unif -> -- On what we subs
            UnifEq -> 
            UnifEq
    subsEq ident replaceUnif (UnifEq (lUnif, rUnif)) =
        UnifEq ((subsUnif lUnif ident replaceUnif), (subsUnif rUnif ident replaceUnif))

-- S is UnifArrow S1 -> S2 && T is UnifArrow T1 -> T2 => unify(C' ∪ {S1 = T1} ∪ {S2 = T2})
unifSolve (UnifEq ((UnifArrow s1 s2), (UnifArrow t1 t2)) : xs) =
    unifSolve (xs ++ [UnifEq (s1, t1), UnifEq (s2, t2)])

-- else FAIL
unifSolve _ = Left ERROR_UNIF_FAIL
