module Stella.TypeCheck where

import Stella.Abs
import Stella.ErrM

import Data.Maybe
import Prelude

-- Порефакторить систему сборки

-- Проверить требования для ядра языкаNatRec
-- Для NatRec вылизать реализацию, в abstraction тупо переиспользование кода DeclFun
-- Функции как значения первого класса (толькосоднимпараметром): Abstraction


-- TypeUnit, ConstUnit              #unit-type
-- TypeTuple, Tuple, DotTuple       #pairs
-- TypeRecord, Record, DotRecord    #records
-- Let, APatternBinding, PatternVar #let-bindings
-- #type-ascriptions: TypeAsc
-- #sum-types: TypeSum, Inl, Inr, Match, AMatchCase, PatternInl, PatternInr, PatternVar
-- #lists: TypeList, List, ConsList, Head, Tail, IsEmpty
-- #variants:TypeVariant,AVariantFieldType,SomeTyping,Variant,SomeExprData,
-- PatternVariant, SomePatternData
-- #fixpoint-combinator: Fix

-- T-Sub??

-- Окружение: имя переменной → её тип
type Env = [(StellaIdent, Type)]

data CErrType
    = ERROR_NOT_IMPLEMENTED_YET
    | ERROR_MISSING_MAIN
    | ERROR_UNDEFINED_VARIABLE StellaIdent
    | ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION Expr Type Type -- Expr Expected Got
    | ERROR_NOT_A_FUNCTION
  deriving (Eq, Ord, Show, Read)

data CheckResult = CheckOk | CheckErr CErrType
  deriving (Show, Eq)

-- Вспомогательная функция для T-App
exprListCheck :: Env -> [Expr] -> [Type] -> CheckResult
exprListCheck env (e:etail) (ty:tys) =
    case exprCheck env e ty of
        CheckOk ->
            exprListCheck env etail tys
        
        CheckErr err ->
            CheckErr err

exprListCheck _ [] [] = CheckOk
exprListCheck _ _ _ = CheckErr ERROR_NOT_IMPLEMENTED_YET


-- T-Abs
declCheck :: Env -> Decl -> Type -> CheckResult
declCheck _ (DeclFun _ name _ retAnn _ _ expr) (TypeFun _ retType) =
    case retAnn of
        NoReturnType ->
            if (retType == TypeBottom) -- TODO: Точно ли чекать на TypeBottom?
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION expr TypeBottom retType)

        SomeReturnType annTy ->
            if retType == annTy
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION expr annTy retType)

declCheck _ d _ = CheckErr ERROR_NOT_IMPLEMENTED_YET

-- T-Var
exprCheck :: Env -> Expr -> Type -> CheckResult
exprCheck env expr@(Var ident) expectedTy =
    case lookup ident env of
        Just identTy ->
            if identTy == expectedTy
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION expr expectedTy identTy)

        Nothing -> CheckErr (ERROR_UNDEFINED_VARIABLE ident)

exprCheck _ e _ = CheckErr ERROR_NOT_IMPLEMENTED_YET
