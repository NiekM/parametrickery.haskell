{-# LANGUAGE AllowAmbiguousTypes #-}

{- |
Module      : Data.SBV.Refine
Copyright   : (c) Anonymous 2024
Maintainer  : Anonymous

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

-- TODO: rewrite using RequiredTypeArguments i.o. AllowAmbiguousTypes
class Encode a => Ref a where
  refine :: SBV (Sym a) -> SBool

  default refine :: (a ~ Sym a) => SBV (Sym a) -> SBool
  refine _ = sTrue

instance Ref ()
instance Ref Char
instance Ref Bool
instance Ref Int where
  refine _ = sTrue

instance Ref Void where
  refine _ = sFalse

instance Ref Natural where
  refine n = n .>= 0

instance (Ref a, Ref b) => Ref (a, b) where
  refine s = let (x, y) = SBV.untuple s in
    refine @a x .&& refine @b y

instance (Ref a, Ref b) => Ref (Either a b) where
  refine = SBV.either (refine @a) (refine @b)

instance Ref a => Ref (Maybe a) where
  refine = SBV.maybe sTrue (refine @a)
