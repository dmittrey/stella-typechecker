{-# LANGUAGE PatternSynonyms #-}

module Main where

import System.Environment (getArgs)
import System.Exit        (exitFailure)
import System.IO          (hPutStrLn, stderr)

import Stella.Abs
import Stella.Par
import Stella.ErrM

import Stella.TypeCheck.Core
import Stella.TypeCheck.Error
import Stella.TypeCheck.Context
import Stella.TypeCheck.CheckInfer
import Stella.TypeCheck.Unification


-- Мне по суи нужно сначала найти какой тип декларации, если тип декларации useExnTypeDecl, то обходим такие декларации и 
typeCheck :: Program -> IO ()
typeCheck (AProgram _ exts decls) =
    let exnCtx0 = if useExnTypeDecl
                then foldl stepExnTypeDecl ExnTypeNotDeclared decls
                else ExnTypeNotDeclared
        exnCtx  = if useOpenVariantExn
                then foldl stepOpenVariantExn exnCtx0 decls
                else exnCtx0

    in
        -- putStrLn $ "Type error: " ++ show exnCtx
        case (foldl stepCheck (CheckOk, Env { envVars = [], envExn = exnCtx, isAmbTyAsBot = useAmbTyAsBot, isSubtyping = useSubtyping }) decls) of
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

    useAmbTyAsBot :: Bool
    useAmbTyAsBot = any (\(AnExtension ns) -> any (\(ExtensionName n) -> n == "#ambiguous-type-as-bottom") ns) exts

    useSubtyping :: Bool
    useSubtyping = any (\(AnExtension ns) -> any (\(ExtensionName n) -> n == "#structural-subtyping") ns) exts

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
    stepCheck (CheckErr err, env) decl =
        (CheckErr err, env)
    stepCheck (CheckOk, env) decl =
        declCheck env decl

-- runTest :: String -> [UnifEq] -> IO ()
-- runTest name eqs = do
--     putStrLn ("=== " ++ name ++ " ===")
--     case unifSolve eqs of
--         Left err   -> putStrLn ("Error: " ++ show err)
--         Right subs -> putStrLn (show subs)

-- main :: IO ()
-- main = do
--     let tNat = aUnifType TypeNat
--         x = aUnifVar "X"
--         y = aUnifVar "Y"

--     -- 1) X = Nat, Y = X -> X  => Y = Nat -> Nat, X = Nat
--     runTest "basic arrow" [ UnifEq (x, tNat), UnifEq (y, aUnifArrow x x) ]

--     -- 2) X = X  trivial
--     runTest "trivial var eq" [ UnifEq (x, x) ]

--     -- 3) occurs-check: X = X -> X  -> should fail (infinite)
--     runTest "occurs-check" [ UnifEq (x, aUnifArrow x x) ]

--     -- 4) type mismatch: Nat = Bool -> fail
--     -- (assuming Type has e.g. TypeBool; adjust to your Type constructors)
--     runTest "type mismatch" [ UnifEq (aUnifType TypeNat, aUnifType TypeBool) ]


-- main :: IO ()
-- main = do
--     let 
--         arg1 = UnifEq (aUnifVar "X", aUnifType TypeNat)
--         arg2 = UnifEq (aUnifVar "Y", aUnifArrow (aUnifVar "X") (aUnifVar "X"))

--         arg3 = UnifEq (aUnifArrow (aUnifType TypeNat) (aUnifType TypeNat), aUnifArrow (aUnifVar "X") (aUnifVar "Y"))

--         arg4 = UnifEq (aUnifArrow (aUnifVar "X") (aUnifVar "Y"), aUnifArrow (aUnifVar "Y") (aUnifVar "Z"))
--         arg5 = UnifEq (aUnifVar "Z", aUnifArrow (aUnifVar "U") (aUnifVar "W"))

--         arg6 = UnifEq (aUnifType TypeNat, aUnifArrow (aUnifType TypeNat) (aUnifVar "Y"))

--         arg7 = UnifEq (aUnifVar "Y", aUnifArrow (aUnifType TypeNat) (aUnifVar "Y"))

--     putStrLn "Test 1:"
--     case unifSolve [arg1, arg2] of
--         Left err   -> putStrLn ("Error: " ++ show err)
--         Right subs -> putStrLn (show subs)

--     putStrLn "Test 2:"
--     case unifSolve [arg3] of
--         Left err   -> putStrLn ("Error: " ++ show err)
--         Right subs -> putStrLn (show subs)

--     putStrLn "Test 3:"
--     case unifSolve [arg4, arg5] of
--         Left err   -> putStrLn ("Error: " ++ show err)
--         Right subs -> putStrLn (show subs)

--     putStrLn "Test 4:"
--     case unifSolve [arg6] of
--         Left err   -> putStrLn ("Error: " ++ show err)
--         Right subs -> putStrLn (show subs)

--     putStrLn "Test 5:"
--     case unifSolve [arg7] of
--         Left err   -> putStrLn ("Error: " ++ show err)
--         Right subs -> putStrLn (show subs)

--     putStrLn "Test 6:"
--     case unifSolve [] of
--         Left err   -> putStrLn ("Error: " ++ show err)
--         Right subs -> putStrLn (show subs)

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
