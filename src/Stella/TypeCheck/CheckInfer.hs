module Stella.TypeCheck.CheckInfer where

-- Результат проверки против типа
type CheckResult = Either CErrType ()

pattern CheckOk :: CheckResult
pattern CheckOk = Right ()

pattern CheckErr :: CErrType -> CheckResult
pattern CheckErr e = Left e

-- Результат вывода чего-то
type InferResult = Either CErrType

pattern InferOk :: a -> InferResult a
pattern InferOk x = Right x

pattern InferErr :: CErrType -> InferResult a
pattern InferErr e = Left e

exprCheck :: Env -> Expr -> Type -> CheckResult



