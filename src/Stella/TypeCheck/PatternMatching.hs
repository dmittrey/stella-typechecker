module Stella.TypeCheck.PatternMatching where

import Stella.TypeCheck.Error
import Stella.TypeCheck.Context
import Stella.TypeCheck.Subsumption

import Stella.Abs

import qualified Data.Map as Map
import qualified Data.Set as Set

data VariantFieldLookupStatus
    = VariantFieldExistSomeType Type
    | VariantFieldExistNoType
    | VariantFieldMissing
  deriving (Eq, Ord, Show, Read)

-- Вспомогательная функция для поиска тега в TypeVariant
lookupVariantField :: StellaIdent -> [VariantFieldType] -> VariantFieldLookupStatus
lookupVariantField ident fields =
    let nameToOptType = [(n, t) | AVariantFieldType n t <- fields]
    in
        case lookup ident nameToOptType of
            Just (SomeTyping t)     -> VariantFieldExistSomeType t
            Just (NoTyping)         -> VariantFieldExistNoType
            Nothing                 -> VariantFieldMissing


-- ====== Bind Type By Pattern ======

-- (-) PatternCastAs Pattern Type
-- (-) PatternAsc Pattern Type
-- (+) PatternVariant StellaIdent PatternData
-- (+) PatternInl Pattern
-- (+) PatternInr Pattern
-- (+) PatternTuple [Pattern]
-- (+) PatternRecord [LabelledPattern]
-- (+) PatternList [Pattern]
-- (+) PatternCons Pattern Pattern
-- (+) PatternFalse
-- (+) PatternTrue
-- (+) PatternUnit
-- (+) PatternInt Integer
-- (+) PatternSucc Pattern
-- (+) PatternVar StellaIdent
bindPattern :: Env -> Pattern -> Type -> InferResult Env

bindPattern env (PatternCastAs pat castTy) ty
    | ty <: castTy  = bindPattern env pat castTy
    | otherwise     = InferErr (ERROR_UNEXPECTED_SUBTYPE ty castTy)

bindPattern env (PatternAsc pat ascTy) ty =
    bindPattern env pat ascTy

bindPattern env (PatternVariant ident patData) (TypeVariant fields) =
    case patData of
        NoPatternData       ->
            case lookupVariantField ident fields of
                VariantFieldExistSomeType ty ->
                    InferErr ERROR_UNEXPECTED_NULLARY_VARIANT_PATTERN
                VariantFieldExistNoType ->
                    InferOk env
                VariantFieldMissing ->
                    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeVariant fields))
        SomePatternData pat ->
            case lookupVariantField ident fields of
                VariantFieldExistSomeType ty ->
                    bindPattern env pat ty
                VariantFieldExistNoType ->
                    InferErr ERROR_UNEXPECTED_NON_NULLARY_VARIANT_PATTERN
                VariantFieldMissing ->
                    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeVariant fields))
bindPattern _   (PatternVariant ident patData) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternInl p) (TypeSum t1 _) =
    bindPattern env p t1
bindPattern _   (PatternInl _) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternInr p) (TypeSum _ t2) =
    bindPattern env p t2
bindPattern _   (PatternInr _) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternTuple pats) (TypeTuple tys) =
    let bindAll e [] [] = InferOk e
        bindAll e (p:ps) (t:ts) =
            bindPattern e p t >>= \e' -> bindAll e' ps ts
        bindAll _ _ _ = InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeTuple tys))
    in bindAll env pats tys
bindPattern _   (PatternTuple _) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternRecord pats) (TypeRecord fields) =
    let identToType = [(i, ty)  | ARecordFieldType i ty <- fields]
        bindAll e [] = InferOk e
        bindAll e ((ALabelledPattern ident identPat):ps) =
            case lookup ident identToType of
                Just ty ->
                    bindPattern e identPat ty >>= \e' -> bindAll e' ps
                Nothing -> InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE (TypeRecord fields))
    in bindAll env pats
bindPattern _   (PatternRecord _) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternList pats) (TypeList ty) =
    let bindAll e [] = InferOk e
        bindAll e (p:ps) =
            bindPattern e p ty >>= \e' -> bindAll e' ps
    in bindAll env pats
bindPattern _   (PatternList _) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternCons patH patT) (TypeList ty) =
    case bindPattern env patH ty of
        InferErr err -> InferErr err
        InferOk env' ->
            bindPattern env' patT (TypeList ty)
bindPattern _   (PatternCons _ _) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env PatternFalse TypeBool =
    InferOk env
bindPattern _   PatternFalse ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env PatternTrue TypeBool =
    InferOk env
bindPattern _   PatternTrue ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env PatternUnit TypeUnit =
    InferOk env
bindPattern _   PatternUnit ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternInt n) TypeNat =
    InferOk env
bindPattern _   (PatternInt n) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternSucc n) TypeNat =
    bindPattern env n TypeNat
bindPattern _   (PatternSucc n) ty =
    InferErr (ERROR_UNEXPECTED_PATTERN_FOR_TYPE ty)

bindPattern env (PatternVar ident) t =
    InferOk env { envVars = (ident, t) : envVars env }