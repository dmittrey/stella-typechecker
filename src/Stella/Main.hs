{-# LANGUAGE PatternSynonyms #-}

module Main where

import System.Environment (getArgs)
import System.Exit        (exitFailure)
import System.IO          (hPutStrLn, stderr)

import Stella.Abs
import Stella.Par
import Stella.ErrM

import Stella.TypeInfer
import Stella.TypeCheck

-- Основная точка входа
typeCheck :: Program -> IO ()
typeCheck (AProgram _ _ decls) =
    case declsCheck [] decls of
        Left err -> putStrLn $ "Type error: " ++ err
        Right _  -> putStrLn "Type checking passed!"

-- Проходим декларации: сначала выводим тип (declInfer),
-- добавляем его в env, затем сверяем аннотацию (declCheck).
declsCheck :: Env -> [Decl] -> Err Env
-- когда декларации закончились
declsCheck env [] =
    case lookup (StellaIdent "main") env of
        Just _  -> Ok env
        Nothing -> Bad $ show ERROR_MISSING_MAIN
-- когда есть ещё декларации
declsCheck env (d:ds) =
    case declInfer env d of
        Ok (name, ty) ->
            let env' = (name, ty) : env
            in
                case declCheck env d ty of
                    CheckOk -> declsCheck env' ds
                    CheckErr err -> Bad $ show err
        Bad msg -> Bad msg

main :: IO ()
main = do
    args <- getArgs
    case args of
        [file] -> do
            source <- readFile file
            case pProgram (myLexer source) of
                Ok ast  -> typeCheck ast
                Bad err -> do
                    hPutStrLn stderr $ "Parse error: " ++ err
                    exitFailure
        _ -> do
            hPutStrLn stderr "Usage: stella <SourceFile>"
            exitFailure
