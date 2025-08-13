module Stella.TypeChecker where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.IO.Class
import Control.Monad (foldM)

import Stella.Abs
import Stella.ErrM

-- Занести проверка/вывод для внутренностей decl?

-- Окружение: имя переменной → её тип
type Env = [(StellaIdent, Type)]

-- Основная точка входа
typeCheck :: Program -> IO ()
typeCheck (AProgram _ _ decls) =
    case checkDecls [] decls of
        Left err -> putStrLn $ "Type error: " ++ err
        Right _  -> putStrLn "Type checking passed!"

-- Проверка списка деклараций
-- Не текут ли локальные переменные?
checkDecls :: Env -> [Decl] -> Err Env
checkDecls env [] = Ok env
checkDecls env (d:ds) = do
    tdecl <- declCheck env d
    let env' = case d of
            DeclFun _ name _ _ _ _ _ ->
                (name, tdecl) : env
            _ -> env
    checkDecls env' ds

-- Проверка одной декларации

-- T-Abs
declCheck :: Env -> Decl -> Err Type
declCheck env (DeclFun _ name params _ _ _ body) =
    let
        paramEnv = [(ident, t) | AParamDecl ident t <- params]
        envWithParams = paramEnv ++ env
    in case exprCheck envWithParams body of
        Ok tfunc  -> Ok (TypeFun [t | AParamDecl _ t <- params] tfunc)
        Bad msg -> Bad $ show msg

declCheck _ (DeclFunGeneric _ _ _ _ _ _ _ _) =
    Bad "DeclFunGeneric not supported"
declCheck _ (DeclTypeAlias _ _) =
    Bad "DeclTypeAlias not supported"
declCheck _ (DeclExceptionType _) =
    Bad "DeclExceptionType not supported"
declCheck _ (DeclExceptionVariant _ _) =
    Bad "DeclExceptionVariant not supported"

-- Проверка выражений
exprCheck :: Env -> Expr -> Err Type

-- Логические выражения

-- T-True
exprCheck _ ConstTrue  = Ok TypeBool
-- T-False
exprCheck _ ConstFalse = Ok TypeBool
-- T-If
exprCheck env (If e1 e2 e3) = do
    t1 <- exprCheck env e1
    t2 <- exprCheck env e2
    t3 <- exprCheck env e3
    case t1 of
        TypeBool ->
            if t2 == t3
                then Ok t2
                else Bad $ "T-If failed. Types t2 and t3 not matched: " ++ show t2 ++ " vs " ++ show t3
        _ -> Bad $ "T-If failed. Condition is not Bool: " ++ show t1

-- Арифметические выражения

-- T-Zero
exprCheck _ (ConstInt 0) = Ok TypeNat
-- T-Succ
exprCheck env (Succ e) = do
    t <- exprCheck env e
    case t of
        TypeNat -> Ok TypeNat
        _       -> Bad $ "T-Succ failed. Expected Nat, got: " ++ show t
-- T-Pred
exprCheck env (Pred e) = do
    t <- exprCheck env e
    case t of
        TypeNat -> Ok TypeNat
        _       -> Bad $ "T-Pred failed. Expected Nat, got: " ++ show t
-- T-IsZero
exprCheck env (IsZero e) = do
    t <- exprCheck env e
    case t of
        TypeNat -> Ok TypeBool
        _       -> Bad $ "T-IsZero failed. Expected Nat, got: " ++ show t

-- \ - Исчисление

-- T-Var
exprCheck env (Var ident) =
    case lookup ident env of
        Just t  -> Ok t
        Nothing -> Bad $ "Unbound variable: " ++ show ident

-- T-App

-- Other
exprCheck _ e = Bad $ "Not implemented: " ++ show e
