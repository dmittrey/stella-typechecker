{-# LANGUAGE PatternSynonyms #-}

module Main where

import System.Environment (getArgs)
import System.Exit        (exitFailure)
import System.IO          (hPutStrLn, stderr)

import Stella.Abs
import Stella.Par
import Stella.ErrM

import Stella.TypeCheck

-- Основная точка входа
typeCheck :: Program -> IO ()
typeCheck (AProgram _ _ decls) =
        let env = []
    in
        case (foldl step (CheckOk, []) decls) of
            ((CheckErr err), env) -> putStrLn $ "Type error: " ++ show err
            (CheckOk, env) -> 
                case lookup (StellaIdent "main") env of
                    Just ident ->
                        putStrLn "Type checking passed!"
                    Nothing ->
                        putStrLn $ "Type error: " ++ show ERROR_MISSING_MAIN
    where
        step :: (CheckResult, Env) -> Decl -> (CheckResult, Env)
        step (CheckOk, env) decl =
            declCheck env decl
        step ((CheckErr err), env) decl =
            (CheckErr err, env)

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
