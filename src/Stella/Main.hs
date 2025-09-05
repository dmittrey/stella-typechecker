{-# LANGUAGE PatternSynonyms #-}

module Main where

import System.Environment (getArgs)
import System.Exit        (exitFailure)
import System.IO          (hPutStrLn, stderr)

import Stella.Abs
import Stella.Par
import Stella.ErrM

import Stella.TypeCheck


-- Мне по суи нужно сначала найти какой тип декларации, если тип декларации useExnTypeDecl, то обходим такие декларации и 
typeCheck :: Program -> IO ()
typeCheck (AProgram _ exts decls) =
    let exnCtx = if useExnTypeDecl
        then foldl stepExnTypeDecl ExnTypeNotDeclared decls
        else if useOpenVariantExn
            then foldl stepOpenVariantExn ExnTypeNotDeclared decls
            else ExnTypeNotDeclared
    in
        case (foldl stepCheck (CheckOk, Env { envVars = [], envExn = exnCtx }) decls) of
            ((CheckErr err), env) -> putStrLn $ "Type error: " ++ show err
            (CheckOk, env) -> 
                case lookup (StellaIdent "main") (envVars env) of
                    Just ident ->
                        putStrLn "Type checking passed!"
                    Nothing ->
                        putStrLn $ "Type error: " ++ show ERROR_MISSING_MAIN

  where
    -- checkForExtension :: [Extension] -> ()
    useExnTypeDecl :: Bool
    useExnTypeDecl = any (\(AnExtension ns) -> any (\(ExtensionName n) -> n == "#exception-type-declaration") ns) exts

    useOpenVariantExn :: Bool
    useOpenVariantExn = any (\(AnExtension ns) -> any (\(ExtensionName n) -> n == "#open-variant-exceptions") ns) exts

    stepExnTypeDecl :: ExnCtx -> Decl -> ExnCtx
    stepExnTypeDecl _ (DeclExceptionType ty) = ExnTypeDecl ty
    stepExnTypeDecl ctx _ = ctx

    stepOpenVariantExn :: ExnCtx -> Decl -> ExnCtx
    stepOpenVariantExn (ExnOpenVariant variants) (DeclExceptionVariant ident ty) = 
        ExnOpenVariant ((AVariantFieldType ident (SomeTyping ty)) : variants)
    stepOpenVariantExn (ExnTypeNotDeclared) (DeclExceptionVariant ident ty) = 
        ExnOpenVariant [(AVariantFieldType ident (SomeTyping ty))]
    stepOpenVariantExn ctx _ = ctx

    -- Проверка функций и других деклараций
    stepCheck :: (CheckResult, Env) -> Decl -> (CheckResult, Env)
    stepCheck (CheckErr err, env) decl =
        (CheckErr err, env)
    stepCheck (CheckOk, env) decl =
        declCheck env decl

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
