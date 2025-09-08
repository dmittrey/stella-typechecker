module Stella.TypeCheck.Subsumption where

import Stella.Abs

import qualified Data.Map as Map
import qualified Data.Set as Set

(<:) :: Type -> Type -> Bool

-- ====== S-Top ======
_ <: TypeTop = True

-- ====== S-Bot ======
TypeBottom <: _ = True

-- ====== S-Sum (ковариантность по каждому элементу) ======
TypeSum l1 l2 <: TypeSum r1 r2 = (l1 <: r1) && (l2 <: r2)

-- ====== S-Tuple (ковариантность по каждому элементу) ======
TypeTuple lTys <: TypeTuple rTys =
    length lTys == length rTys &&
    and [ lTy <: rTy | (lTy, rTy) <- zip lTys rTys ]

-- ====== S-Arrow ======
TypeFun lParams lRet <: TypeFun rParams rRet =
    length lParams == length rParams &&
    and [ rTy <: lTy | (lTy, rTy) <- zip lParams rParams ] &&  -- контравариантность аргументов
    lRet <: rRet                                               -- ковариантность результата

-- ====== S-Record ======
TypeRecord lFields <: TypeRecord rFields =
    let lMap = Map.fromList [(name, ty) | ARecordFieldType name ty <- lFields]
        rMap = Map.fromList [(name, ty) | ARecordFieldType name ty <- rFields]
    in 
        -- S-RecordWidth
        Map.keysSet lMap `Set.isSubsetOf` Map.keysSet rMap &&
        -- S-RecordDepth
        all (\(k,lTy) -> 
                case Map.lookup k rMap of
                    Just rTy -> lTy <: rTy
                    Nothing  -> False) (Map.toList lMap)

-- ====== S-Variant ======
TypeVariant lFields <: TypeVariant rFields =
    let lMap = Map.fromList [(ident, ty) | AVariantFieldType ident (SomeTyping ty) <- lFields]
        rMap = Map.fromList [(ident, ty) | AVariantFieldType ident (SomeTyping ty) <- rFields]
    in
        -- S-VariantWidth
        Map.keysSet lMap `Set.isSubsetOf` Map.keysSet rMap &&
        -- S-VariantDepth
        all (\(k,lTy) -> 
                case Map.lookup k rMap of
                    Just rTy -> lTy <: rTy
                    Nothing  -> False) (Map.toList lMap)

-- ====== S-List ======
TypeList lTy <: TypeList rTy = lTy <: rTy

-- ====== S-Ref ======
TypeRef lTy <: TypeRef rTy  = lTy <: rTy

-- ====== S-Refl ======
t1 <: t2
    | t2 == t2 = True

-- Fallback
_ <: _ = False