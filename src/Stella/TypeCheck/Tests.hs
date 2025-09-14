-- runTest :: String -> UEqs -> IO ()
-- runTest name eqs = do
--     putStrLn ("=== " ++ name ++ " ===")
--     case unifSolve eqs of
--         Left err   -> putStrLn ("Error: " ++ show err)
--         Right subs -> putStrLn ("Result: " ++ show subs)

-- main :: IO ()
-- main = do
--     let tNat = TypeNat
--         x    = TypeVar (StellaIdent "X")
--         y    = TypeVar (StellaIdent "Y")
--         z    = TypeVar (StellaIdent "Z")
--         u    = TypeVar (StellaIdent "U")
--         w    = TypeVar (StellaIdent "W")

--     -- Test 1: X = Nat, Y = X -> X
--     runTest "Test 1" [ (x, tNat), (y, TypeFun [x] x) ]

--     -- Test 2: (Nat -> Nat) = X -> Y
--     runTest "Test 2" [ (TypeFun [tNat] tNat, TypeFun [x] y) ]

--     -- Test 3: (X -> Y) = (Y -> Z), Z = U -> W
--     runTest "Test 3" [ (TypeFun [x] y, TypeFun [y] z), (z, TypeFun [u] w) ]

--     -- Test 4: Nat = Nat -> Y  (should fail)
--     runTest "Test 4" [ (tNat, TypeFun [tNat] y) ]

--     -- Test 5: Y = Nat -> Y  (occurs check, should fail)
--     runTest "Test 5" [ (y, TypeFun [tNat] y) ]

--     -- Test 6: empty constraints
--     runTest "Test 6" []




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