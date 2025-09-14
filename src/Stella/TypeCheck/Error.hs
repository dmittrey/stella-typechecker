{-# LANGUAGE PatternSynonyms #-}

module Stella.TypeCheck.Error where

import Stella.Abs

import Stella.TypeCheck.Unification

-- Результат проверки против типа
type CheckResult = Either CErrType UEqs

pattern CheckOk :: UEqs -> CheckResult
pattern CheckOk e = Right e

pattern CheckErr :: CErrType -> CheckResult
pattern CheckErr e = Left e

-- Результат вывода чего-то
type InferResult = Either CErrType

pattern InferOk :: a -> InferResult a
pattern InferOk x = Right x

pattern InferErr :: CErrType -> InferResult a
pattern InferErr e = Left e

-- Тип ошибок для Pattern Matching
data MatchErrType 
    = NotSeenZero
    | NotSeenSucc
    | NotSeenTrue
    | NotSeenFalse
    | NotSeenLeftInjection
    | NotSeenRightInjection
    | NotSeenAllLabels
    | NotSeenEmptyList
    | NotSeenConsList
    | NotSeenAllTuple
    | NotSeenAllRecord
  deriving (Eq, Ord, Show, Read)