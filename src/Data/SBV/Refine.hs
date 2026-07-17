{- |
Module      : Data.SBV.Refine
Copyright   : (c) Niek Mulleners 2024
Maintainer  : Niek Mulleners

Refinement types using symbolic representations.

-}
module Data.SBV.Refine
  ( module Data.SBV.Encode
  , Ref(..)
  ) where

import Data.SBV
import Data.SBV.Tuple  qualified as SBV
import Data.SBV.Either qualified as SBV
import Data.SBV.Maybe  qualified as SBV

import Data.SBV.Encode

import Base

-- | The class 'Ref' defines a refinement type, by describing how the symbolic
-- encoding is constrained using 'refine'.

class Encode a => Ref a where
  refine :: forall b -> (a ~ b) => SBV (Sym b) -> SBool

  default refine :: forall b -> (a ~ b) => SBV (Sym b) -> SBool
  refine _ _ = sTrue

instance Ref ()
instance Ref Char
instance Ref Bool
instance Ref Int where
  refine _ _ = sTrue

instance Ref Void where
  refine _ _ = sFalse

instance Ref Natural where
  refine _ n = n .>= 0

instance (Ref a, Ref b) => Ref (a, b) where
  refine _ s = let (x, y) = SBV.untuple s in
    refine a x .&& refine b y

instance (Ref a, Ref b) => Ref (Either a b) where
  refine _ = SBV.either (refine a) (refine b)

instance Ref a => Ref (Maybe a) where
  refine _ = SBV.maybe sTrue (refine a)
