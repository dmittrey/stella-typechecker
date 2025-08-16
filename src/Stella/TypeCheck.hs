module Stella.TypeCheck where

import Stella.Abs
import Stella.ErrM

import Data.Maybe
import Prelude

-- TODO
-- Порефакторить систему сборки
-- Насытить TypeCheck чтобы руками не проверять

-- 3. для расширений #pairs и #tuples: TypeTuple, Tuple, DotTuple
-- 4. для расширения #records: TypeRecord, Record, DotRecord
-- 5. для расширения #let-bindings: Let, APatternBinding, PatternVar
-- 6. для расширения #type-ascriptions: TypeAsc

-- Окружение: имя переменной → её тип
type Env = [(StellaIdent, Type)]

data CErrType
    = C_ERROR_EXPR_NOT_IMPLEMENTED_YET Expr Type
    | I_ERROR_EXPR_NOT_IMPLEMENTED_YET Expr
    | C_ERROR_DECL_NOT_IMPLEMENTED_YET Decl
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

declCheck _ d _ = CheckErr (C_ERROR_DECL_NOT_IMPLEMENTED_YET d)

exprCheck :: Env -> Expr -> Type -> CheckResult
exprCheck env expr@(Var ident) expectedTy =
    case lookup ident env of
        Just identTy ->
            if identTy == expectedTy
            then CheckOk
            else CheckErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION expr expectedTy identTy)

        Nothing -> CheckErr (ERROR_UNDEFINED_VARIABLE ident)

exprCheck _ _ _ = CheckOk
