{-# LANGUAGE AllowAmbiguousTypes #-}

{- |
Module      : Data.SBV.Refine
Copyright   : (c) Niek Mulleners 2024
Maintainer  : n.mulleners@uu.nl

Refinement types.

-}
module Data.SBV.Refine
  ( module Data.SBV.Encode
  , Ref(..)
  , refHolds
  ) where

import Data.SBV
import Data.SBV.Tuple  qualified as SBV
import Data.SBV.Either qualified as SBV
import Data.SBV.Maybe  qualified as SBV

import Data.SBV.Encode

import Base

-- TODO: rewrite using RequiredTypeArguments i.o. AllowAmbiguousTypes
class Encode a => Ref a where
  ref :: SBV (Sym a) -> SBool

  default ref :: (a ~ Sym a) => SBV (Sym a) -> SBool
  ref _ = sTrue

instance Ref ()
instance Ref Char
instance Ref Bool
instance Ref Int where
  ref _ = sTrue

instance Ref Void where
  ref _ = sFalse

instance Ref Natural where
  ref n = n .>= 0

instance (Ref a, Ref b) => Ref (a, b) where
  ref s = let (x, y) = SBV.untuple s in
    ref @a x .&& ref @b y

instance (Ref a, Ref b) => Ref (Either a b) where
  ref = SBV.either (ref @a) (ref @b)

instance Ref a => Ref (Maybe a) where
  ref = SBV.maybe sTrue (ref @a)

-- | Properties

refHolds :: forall a. Ref a => a -> Bool
refHolds x = case unliteral (ref @a $ literal $ encode x) of
  Nothing -> error "Something went wrong: somehow not a literal"
  Just b -> b
