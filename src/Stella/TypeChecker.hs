module Stella.TypeChecker where

import Stella.Abs
import Stella.ErrM
import Control.Monad (foldM)

-- Типы для тайпчекера (чтобы не конфликтовать с AST.Type — называем TCType)
data TCType = TInt | TBool | TString
  deriving (Show, Eq)

type Env = [(StellaIdent, TCType)]

typeCheck :: Program -> Err ()
typeCheck prog =
    case checkProg [] prog of
        Ok _    -> Ok ()
        Bad err -> Bad err

-- Обход программы
checkProg :: Env -> Program -> Err Env
checkProg env (AProgram _ _ decls) = foldM checkDecl env decls

-- Пока проверяем только DeclFun
checkDecl :: Env -> Decl -> Err Env
checkDecl env (DeclFun _ name _ _ _ _ body) = do
    _ <- inferExpr env body
    return ((name, TInt) : env)  -- заглушка: считаем, что функция возвращает Int
checkDecl env _ = Ok env  -- остальные декларации пока пропускаем

-- Инференс типов для выражений
inferExpr :: Env -> Expr -> Err TCType
inferExpr _   (ConstInt _)  = return TInt
inferExpr _   ConstTrue     = return TBool
inferExpr _   ConstFalse    = return TBool

inferExpr env (Add e1 e2) = do
    t1 <- inferExpr env e1
    t2 <- inferExpr env e2
    if t1 == TInt && t2 == TInt
        then return TInt
        else Bad "Type error in addition"

inferExpr env (Var x) =
    case lookup x env of
        Just t  -> return t
        Nothing -> Bad ("Unbound variable: " ++ show x)

-- Остальные выражения пока не реализованы
inferExpr _ expr = Bad ("Type inference not implemented for: " ++ show expr)
