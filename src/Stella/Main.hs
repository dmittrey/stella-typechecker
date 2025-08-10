{-# LANGUAGE PatternSynonyms #-}

module Main where

import System.Environment (getArgs)
import System.Exit        (exitFailure)
import System.IO          (hPutStrLn, stderr)

import Stella.Abs
import Stella.Par
import Stella.ErrM (Err, pattern Ok, pattern Bad)
import Stella.TypeChecker (typeCheck)

main :: IO ()
main = do
    args <- getArgs
    case args of
        [file] -> do
            source <- readFile file
            case pProgram (myLexer source) of
                Ok ast ->
                    case typeCheck ast of
                        Ok _    -> putStrLn "Type check OK"
                        Bad err -> putStrLn $ "Type error: " ++ err
                Bad err -> putStrLn $ "Parse error: " ++ err
        _ -> do
            hPutStrLn stderr "Usage: stella <SourceFile>"
            exitFailure
