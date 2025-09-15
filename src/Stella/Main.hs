{-# LANGUAGE PatternSynonyms #-}

module Main where

import System.Environment (getArgs)
import System.Exit        (exitFailure)
import System.IO          (hPutStrLn, stderr)

import Stella.Abs
import Stella.Par
import Stella.ErrM

import Stella.TypeCheck.Core
import Stella.TypeCheck.Result
import Stella.TypeCheck.Error
import Stella.TypeCheck.Context
import Stella.TypeCheck.CheckInfer
import Stella.TypeCheck.Unification

import Debug.Trace

typeCheck :: Program -> IO ()
typeCheck (AProgram _ exts decls) =
    -- trace (show decls) $
    let exnCtx0 = if useExnTypeDecl
                then foldl stepExnTypeDecl ExnTypeNotDeclared decls
                else ExnTypeNotDeclared
        exnCtx  = if useOpenVariantExn
                then foldl stepOpenVariantExn exnCtx0 decls
                else exnCtx0
        env0 = Env { envVars = [], envExn = exnCtx, isAmbTyAsBot = useAmbTyAsBot, isSubtyping = useSubtyping, isReconstruction = useReconstruction }
        (checkRes, env) = foldl stepCheck (CheckOk emptyUEqs, env0) decls
    in
        -- putStrLn $ "Type error: " ++ show exnCtx
        case checkRes of
            CheckErr err ->
                putStrLn $ "Type error: " ++ show err
            CheckOk unifEqs -> 
                case lookup (StellaIdent "main") (envVars env) of
                    Just _ ->
                        trace (show unifEqs) $
                        case unifSolve unifEqs of
                            Left err    -> putStrLn $ "Type error: " ++ show err
                            Right subs  -> do
                                putStrLn "Type checking passed!"
                                -- putStrLn $ "Substitutions:\n" ++ show subs
                    Nothing ->
                        putStrLn $ "Type error: " ++ show ERROR_MISSING_MAIN

  where
    useExnTypeDecl :: Bool
    useExnTypeDecl = any (\(AnExtension ns) -> any (\(ExtensionName n) -> n == "#exception-type-declaration") ns) exts

    useOpenVariantExn :: Bool
    useOpenVariantExn = any (\(AnExtension ns) -> any (\(ExtensionName n) -> n == "#open-variant-exceptions") ns) exts

    useAmbTyAsBot :: Bool
    useAmbTyAsBot = any (\(AnExtension ns) -> any (\(ExtensionName n) -> n == "#ambiguous-type-as-bottom") ns) exts

    useSubtyping :: Bool
    useSubtyping = any (\(AnExtension ns) -> any (\(ExtensionName n) -> n == "#structural-subtyping") ns) exts

    useReconstruction :: Bool
    useReconstruction = any (\(AnExtension ns) -> any (\(ExtensionName n) -> n == "#type-reconstruction") ns) exts

    stepExnTypeDecl :: ExceptionContext -> Decl -> ExceptionContext
    stepExnTypeDecl _ (DeclExceptionType ty) = ExnTypeDecl ty
    stepExnTypeDecl ctx _ = ctx

    stepOpenVariantExn :: ExceptionContext -> Decl -> ExceptionContext
    stepOpenVariantExn (ExnOpenVariant variants) (DeclExceptionVariant ident ty) = 
        ExnOpenVariant ((AVariantFieldType ident (SomeTyping ty)) : variants)
    stepOpenVariantExn (ExnTypeNotDeclared) (DeclExceptionVariant ident ty) = 
        ExnOpenVariant [(AVariantFieldType ident (SomeTyping ty))]
    stepOpenVariantExn ctx _ = ctx

    -- Проверка функций и других деклараций
    stepCheck :: (CheckResult, Env) -> Decl -> (CheckResult, Env)
    stepCheck (CheckErr err, envAcc) _ = (CheckErr err, envAcc)
    stepCheck (CheckOk c, envAcc) d =
        let (res, envAcc') = declCheck envAcc d
        in case res of
             Left err      -> (CheckErr err, envAcc')
             Right newEqs  -> (CheckOk (c <> newEqs), envAcc')

main :: IO ()
main = do
    args <- getArgs
    case args of
        [file] -> do
            source <- readFile file
            case pProgram (myLexer source) of
                Ok ast  -> typeCheck (freshProgram 0 ast)
                Bad err -> do
                    hPutStrLn stderr $ "Parse error: " ++ err
                    exitFailure
        _ -> do
            hPutStrLn stderr "Usage: stella <SourceFile>"
            exitFailure
