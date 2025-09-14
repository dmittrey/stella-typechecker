{-# LANGUAGE PatternSynonyms #-}

module Stella.TypeCheck.Error where

import Stella.Abs

import Stella.TypeCheck.Unification

-- Результат проверки против типа
type CheckResult = Either CErrType UnifEqs

pattern CheckOk :: UnifEqs -> CheckResult
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

-- Типы ошибок при проверке типов
data CErrType
    -- Собственные ошибки
    = ERROR_DECL_CHECK_NOT_IMPLEMENTED Decl
    | ERROR_EXPR_CHECK_NOT_IMPLEMENTED Expr Type
    | ERROR_EXPR_INFER_NOT_IMPLEMENTED Expr
    | ERROR_PATTERN_NOT_SUPPORTED Pattern Type
    | ERROR_MATCH_NOT_SUPPORTED Type
    | MONAD_FAIL_NOT_GUARDED_IM_BEGINNING_SORRY

    -- Требуемые ошибки
    | ERROR_AMBIGUOUS_PATTERN_TYPE Pattern
    | ERROR_MISSING_MAIN
    | ERROR_UNDEFINED_VARIABLE StellaIdent
    | ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION Expr Type Type -- Expr Expected Got
    | ERROR_NOT_A_FUNCTION Expr
    | ERROR_NOT_A_TUPLE Expr
    | ERROR_NOT_A_RECORD Expr
    | ERROR_UNEXPECTED_LAMBDA Expr Type
    | ERROR_UNEXPECTED_TYPE_FOR_PARAMETER StellaIdent Type Type -- Ident Expected Got
    | ERROR_UNEXPECTED_TUPLE Expr Type
    | ERROR_UNEXPECTED_RECORD Expr Type
    | ERROR_UNEXPECTED_VARIANT
    | ERROR_UNEXPECTED_LIST Expr
    | ERROR_UNEXPECTED_INJECTION Expr
    | ERROR_MISSING_RECORD_FIELDS
    | ERROR_UNEXPECTED_RECORD_FIELDS
    | ERROR_UNEXPECTED_FIELD_ACCESS Expr StellaIdent
    | ERROR_UNEXPECTED_VARIANT_LABEL StellaIdent
    | ERROR_TUPLE_INDEX_OUT_OF_BOUNDS Expr Integer
    | ERROR_UNEXPECTED_TUPLE_LENGTH
    | ERROR_AMBIGUOUS_SUM_TYPE Expr
    | ERROR_AMBIGUOUS_VARIANT_TYPE Expr
    | ERROR_AMBIGUOUS_LIST_TYPE
    | ERROR_NOT_A_LIST Type
    | ERROR_ILLEGAL_EMPTY_MATCHING
    | ERROR_NONEXHAUSTIVE_MATCH_PATTERNS [MatchCase]
    | ERROR_UNEXPECTED_PATTERN_FOR_TYPE Type
    | ERROR_DUPLICATE_RECORD_FIELDS
    | ERROR_DUPLICATE_RECORD_TYPE_FIELDS
    | ERROR_DUPLICATE_VARIANT_TYPE_FIELDS Type
    | ERROR_INCORRECT_ARITY_OF_MAIN
    | ERROR_INCORRECT_NUMBER_OF_ARGUMENTS
    | ERROR_UNEXPECTED_NUMBER_OF_PARAMETERS_IN_LAMBDA
    | ERROR_UNEXPECTED_DATA_FOR_NULLARY_LABEL
    | ERROR_MISSING_DATA_FOR_LABEL
    | ERROR_UNEXPECTED_NON_NULLARY_VARIANT_PATTERN
    | ERROR_UNEXPECTED_NULLARY_VARIANT_PATTERN
    | ERROR_NOT_A_REFERENCE Expr
    | ERROR_UNEXPECTED_MEMORY_ADDRESS String
    | ERROR_AMBIGUOUS_REFERENCE_TYPE
    | ERROR_AMBIGUOUS_PANIC_TYPE
    | ERROR_EXCEPTION_TYPE_NOT_DECLARED Expr
    | ERROR_AMBIGUOUS_THROW_TYPE
    | ERROR_UNEXPECTED_SUBTYPE Type Type -- SubType Type
    | ERROR_UNEXPECTED_REFERENCE
    | DEBUG Type
    | DEBUGG Expr
  deriving (Eq, Ord, Show, Read)