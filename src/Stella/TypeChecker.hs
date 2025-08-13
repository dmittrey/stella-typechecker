module Stella.TypeChecker where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.IO.Class
import Control.Monad (foldM)

import Stella.Abs
import Stella.ErrM

-- Интегрировать ErrorCodes
-- Доделать интеграцию T-Abs, T-App

-- Окружение: имя переменной → её тип
type Env = [(StellaIdent, Type)]

-- Основная точка входа
typeCheck :: Program -> IO ()
typeCheck (AProgram _ _ decls) =
    case declsInfer [] decls of
        Left err -> putStrLn $ "Type error: " ++ err
        Right _  -> putStrLn "Type checking passed!"

-- Проверка списка деклараций с запоминанием типов функций
declsInfer :: Env -> [Decl] -> Err Env
declsInfer env [] = Ok env
declsInfer env (d:ds) =
    case declInfer env d of
        Ok (name, ty) ->
            let env' = (name, ty) : env
            in declsInfer env' ds
        Bad msg -> Bad msg

-- Проверка одной декларации

-- T-Abs
declInfer :: Env -> Decl -> Err (StellaIdent, Type)
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

declCheck :: Env -> Decl -> Type -> Err Bool
declCheck env (DeclFun _ name params _ _ _ body) (TypeFun paraml retType) =
    let
        paramEnv = [(ident, t) | AParamDecl ident t <- params]
        envWithParams = paramEnv ++ env
    in case exprCheck envWithParams body retType of
        Ok flag ->
            if (flag == True)
            then Ok True
            else Bad $ "Type check err: Body type mismatch: " ++ show retType
        Bad msg -> Bad msg

-- Вывод типа выражения
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


exprCheck :: Env -> Expr -> Type -> Err Bool
exprCheck env (Var ident) exprType =
    case lookup ident env of
        Just t  -> 
            if (t == exprType)
            then Ok True
            else Bad $ ("Type mismatch: " ++ show t ++ " vs " ++ show exprType)
        Nothing -> Bad $ "Unbound variable: " ++ show ident

exprCheck _ e _ = Bad $ "Type check err: Not implemented yet: " ++ show e
