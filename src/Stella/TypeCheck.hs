module Stella.TypeCheck where

import Stella.TypeInfer

import Stella.Abs
import Stella.ErrM

-- Интегрировать ErrorCodes
-- Доделать интеграцию T-App

-- Основная точка входа
typeCheck :: Program -> IO ()
typeCheck (AProgram _ _ decls) =
    case declsCheck [] decls of
        Left err -> putStrLn $ "Type error: " ++ err
        Right _  -> putStrLn "Type checking passed!"

declsCheck :: Env -> [Decl] -> Err Env
declsCheck env [] = Ok env
declsCheck env (d:ds) =
    case declInfer env d of
        Ok (name, ty) ->
            let env' = (name, ty) : env
            in
                case declCheck env d ty of
                    Ok True -> declsCheck env' ds
                    Ok False -> Bad $ "Type mismatch for " ++ show name ++ " decl." ++ show ty
                    Bad msg -> Bad msg

-- T-Abs
declCheck :: Env -> Decl -> Type -> Err Bool
declCheck env (DeclFun _ name params retTy _ _ body) (TypeFun paraml retType) =
    case retTy of
        NoReturnType -> 
            if (retType == TypeBottom)
            then Ok True
            else Bad $ ("Type mismatch: " ++ show name ++ " expected: " ++ retType ++ ", actual: " ++ TypeBottom)
        SomeReturnType ty ->
            if (retType == ty)
            then Ok True
            else Bad $ ("Type mismatch: " ++ show name ++ " expected: " ++ retType ++ ", actual: " ++ ty)

-- T-Var
exprCheck :: Env -> Expr -> Type -> Err Bool
exprCheck env (Var ident) exprType =
    case lookup ident env of
        Just t  -> 
            if (t == exprType)
            then Ok True
            else Bad $ ("Type mismatch: " ++ show t ++ " vs " ++ show exprType)
        Nothing -> Bad $ "Unbound variable: " ++ show ident

exprCheck _ e _ = Bad $ "Type check err: Not implemented yet: " ++ show e
