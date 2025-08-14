module Stella.TypeInfer where

import Stella.Abs
import Stella.ErrM

-- Окружение: имя переменной → её тип
type Env = [(StellaIdent, Type)]

declInfer :: Env -> Decl -> Err (StellaIdent, Type)
-- T-Abs
declInfer env (DeclFun _ name params _ _ _ body) =
    let paramEnv       = [(ident, t) | AParamDecl ident t <- params]
        envWithParams  = paramEnv ++ env
    in case exprInfer envWithParams body of
        Ok tfunc -> Ok (name, TypeFun [t | AParamDecl _ t <- params] tfunc)
        Bad msg  -> Bad msg

declInfer _ (DeclFunGeneric _ _ _ _ _ _ _ _) =
    Bad "DeclFunGeneric not supported"
declInfer _ (DeclTypeAlias _ _) =
    Bad "DeclTypeAlias not supported"
declInfer _ (DeclExceptionType _) =
    Bad "DeclExceptionType not supported"
declInfer _ (DeclExceptionVariant _ _) =
    Bad "DeclExceptionVariant not supported"

exprInfer :: Env -> Expr -> Err Type
-- T-True
exprInfer _ ConstTrue  = Ok TypeBool
-- T-False
exprInfer _ ConstFalse = Ok TypeBool
-- T-If
exprInfer env (If e1 e2 e3) = do
    t1 <- exprInfer env e1
    t2 <- exprInfer env e2
    t3 <- exprInfer env e3
    case t1 of
        TypeBool ->
            if t2 == t3
                then Ok t2
                else Bad $ "T-If failed. Types t2 and t3 not matched: " ++ show t2 ++ " vs " ++ show t3
        _ -> Bad $ "T-If failed. Condition is not Bool: " ++ show t1

-- T-Zero
exprInfer _ (ConstInt 0) = Ok TypeNat
-- T-Succ
exprInfer env (Succ e) = do
    t <- exprInfer env e
    case t of
        TypeNat -> Ok TypeNat
        _       -> Bad $ "T-Succ failed. Expected Nat, got: " ++ show t
-- T-Pred
exprInfer env (Pred e) = do
    t <- exprInfer env e
    case t of
        TypeNat -> Ok TypeNat
        _       -> Bad $ "T-Pred failed. Expected Nat, got: " ++ show t
-- T-IsZero
exprInfer env (IsZero e) = do
    t <- exprInfer env e
    case t of
        TypeNat -> Ok TypeBool
        _       -> Bad $ "T-IsZero failed. Expected Nat, got: " ++ show t

-- T-Var
exprInfer env (Var ident) =
    case lookup ident env of
        Just t  -> Ok t
        Nothing -> Bad $ "Unbound variable: " ++ show ident

-- T-App
exprInfer env (Application e (elist : elistxs)) = do
    t1 <- exprInfer env e
    t2 <- exprInfer env elist
    case t1 of
        TypeFun (arg:args) ret ->
            if t2 == arg
                then 
                    if null elistxs
                        then Ok ret
                        else exprInfer env (Application (Application e [elist]) elistxs)
                else Bad $ "T-App failed. Expected arg type: " ++ show arg ++ ", got: " ++ show t2
        _ -> Bad $ "T-App failed. Not a function type: " ++ show t1

-- Other
exprInfer _ e =
    Bad $ "Type infer err: Not implemented yet: " ++ show e
