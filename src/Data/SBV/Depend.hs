{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{- |
Module      : Data.SBV.Depend
Copyright   : (c) Niek Mulleners 2024
Maintainer  : n.mulleners@uu.nl

Dependent types.

-}
module Data.SBV.Depend
  ( module Data.SBV.Encode
  , module Data.SBV.Refine
  , Dep(..)
  , depHolds
  , May(..)
  , Fin(..)
  , OR(..)
  , XOR(..)
  ) where

import Data.SBV

import Data.SBV.Encode
import Data.SBV.Refine

import Data.SBV.Tuple  qualified as SBV
import Data.SBV.Either qualified as SBV

import Base

-- TODO: rewrite using RequiredTypeArguments i.o. AllowAmbiguousTypes
class (Encode a, Ref (Arg a)) => Dep a where
  type Arg a :: Type
  dep :: SBV (Sym (Arg a)) -> SBV (Sym a) -> SBool

instance (Ref a, Ref b) => Dep (Const a b) where
  type Arg (Const a b) = b
  dep _ = ref @a

-- TODO: move these to separate files.

newtype May = May ()
  deriving stock (Eq, Ord, Show)
  deriving newtype Encode

instance Dep May where
  type Arg May = Bool
  dep m _ = m .== sTrue

newtype Fin = Fin Natural
  deriving newtype (Eq, Ord, Enum, Show, Num, Encode)

instance Dep Fin where
  type Arg Fin = Natural
  dep n x = x .>= 0 .&& x .< n

newtype OR a b = OR (Either a b)
  deriving newtype (Eq, Ord, Show, Encode)

instance (Dep a, Dep b) => (Dep (OR a b)) where
  type Arg (OR a b) = (Arg a, Arg b)
  dep t = SBV.either (dep @a x) (dep @b y)
    where (x, y) = SBV.untuple t

newtype XOR a b = XOR { unXOR :: Either a b }
  deriving newtype (Eq, Ord, Show, Encode)

instance (Dep a, Dep b) => (Dep (XOR a b)) where
  type Arg (XOR a b) = Either (Arg a) (Arg b)
  dep e d =
    SBV.either
    (\l -> SBV.isLeft  d .&& dep @a l (SBV.fromLeft  d))
    (\r -> SBV.isRight d .&& dep @b r (SBV.fromRight d))
    e

-- | Properties

depHolds :: forall a. Dep a => Arg a -> a -> Bool
depHolds x y = case unliteral (dep @a x' y') of
  Nothing -> error "Something went wrong: somehow not a literal"
  Just b -> b
  where
    x' = literal (encode x)
    y' = literal (encode y)
