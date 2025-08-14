{-# LANGUAGE PatternSynonyms #-}

module Main where

import System.Environment (getArgs)
import System.Exit        (exitFailure)
import System.IO          (hPutStrLn, stderr)

import Stella.Abs
import Stella.Par
import Stella.ErrM (pattern Ok, pattern Bad)
import Stella.TypeCheck (typeCheck)

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
