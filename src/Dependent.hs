{-# LANGUAGE TypeFamilies #-}

module Dependent (Refined(..), Dependent(..)) where

import Types

import Data.SBV
import Data.SBV.Either qualified as SBV
import Data.SBV.Tuple qualified as SBV
import Numeric.Natural
import Data.Void

class SymVal (UnRefined a) => Refined a where
  type UnRefined a
  unrefine :: a -> UnRefined a
  refine :: proxy a -> SBV (UnRefined a) -> SBool

symbolicR :: Refined a => proxy a -> String -> Symbolic (SBV (UnRefined a))
symbolicR p s = do
  x <- symbolic s
  constrain $ refine p x
  return x

class (Refined a, SymVal (InDependent a b)) => Dependent a b where
  type InDependent a b
  independ :: a -> b -> InDependent a b
  depend :: proxy a b -> SBV (UnRefined a) -> SBV (InDependent a b) -> SBool

symbolicD :: Dependent a b => proxy a b -> SBV (UnRefined a) -> String -> Symbolic (SBV (InDependent a b))
symbolicD p x s = do
  y <- symbolic s
  constrain $ depend p x y
  return y

instance Refined Void where
  type UnRefined Void = Integer
  unrefine = absurd
  refine _ _ = sFalse

instance Refined () where
  type UnRefined () = Integer
  unrefine _ = 0
  refine _ n = n .== 0

instance (Refined a, Refined b) => Refined (a, b) where
  type UnRefined (a, b) = (UnRefined a, UnRefined b)
  unrefine (x, y) = (unrefine x, unrefine y)
  refine _ a = let (x, y) = SBV.untuple a in
    refine @a undefined x .&& refine @b undefined y

instance Refined Natural where
  type UnRefined Natural = Integer
  unrefine = toInteger
  refine _ n = n .>= 0

instance (Refined k, Refined a) => Dependent k (K a) where
  type InDependent k (K a) = UnRefined a
  independ _ (K a) = unrefine a
  depend _ _ x = refine @a undefined x

instance (Dependent a b, Dependent c d) => Dependent (a, c) (Either b d) where
  type InDependent (a, c) (Either b d) = Either (InDependent a b) (InDependent c d)
  independ (x, y) = either (Left . independ x) (Right . independ y)
  depend _ a = let (x, y) = SBV.untuple a in
    SBV.either (depend @a @b undefined x) (depend @c @d undefined y)

instance Dependent Natural Fin where
  type InDependent Natural Fin = Integer
  independ _ (Fin n) = unrefine n
  depend _ m n = n .>= 0 .&& n .< m