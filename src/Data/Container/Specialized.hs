{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{- |
Module      : Data.Container.Specialized
Copyright   : (c) Niek Mulleners 2024
Maintainer  : Niek Mulleners

Specialized implementations of containers that are more efficient than the
standard representations.

See the discussion in Section 6.3 of "Example-Based Reasoning About the
Realizability of Polymorphic Programs".

-}
module Data.Container.Specialized
  ( MaybeList(..)
  , ListPair(..)
  , PairList(..)
  , Dup(..)
  ) where

import Data.Map qualified as Map
import Data.List (genericLength)

import Data.SBV.Tuple qualified as SBV

import Data.Dup
import Data.Fin
import Data.Container.Core
import Data.SBV.Encode
import Data.SBV.Depend

import Base

newtype DecFin = DecFin Natural
  deriving newtype (Eq, Ord, Enum, Num, Show, Encode)

instance Dep DecFin where
  type Arg DecFin = Natural
  depend n = depend @Fin (n - 1)

-- | A type synonym for @'Data.Maybe.Maybe' [a]@ with a container instance
-- \[
-- (n : \textit{Nat}) \triangleright \textit{Fin}\ (n - 1)
-- \]
newtype MaybeList a = MaybeList (Maybe [a])
  deriving stock (Eq, Ord, Show)
  deriving stock Functor

instance Container MaybeList where
  type Shape    MaybeList = Natural
  type Position MaybeList = DecFin

  toContainer (MaybeList Nothing) = Extension 0 mempty
  toContainer (MaybeList (Just xs)) = Extension
    { shape = genericLength xs
    , position = Map.fromList (zip [0..] xs)
    }
  fromContainer (Extension 0 _) = MaybeList Nothing
  fromContainer (Extension _ p) = MaybeList . Just $ Map.elems p

newtype SumFin = FinPair Natural
  deriving newtype (Eq, Ord, Enum, Show, Num, Encode)

instance Dep SumFin where
  type Arg SumFin = (Natural, Natural)
  depend n = depend @Fin (a + b)
    where (a, b) = SBV.untuple n

-- | A type synonym for @([a], [a])@ with a container instance
-- \[
-- ((n, m) : \textit{Nat} \times \textit{Nat})
-- \triangleright \textit{Fin}\ (n + m)
-- \]
newtype ListPair a = ListPair ([a], [a])
  deriving stock (Eq, Ord, Show)
  deriving stock Functor

instance Container ListPair where
  type Shape    ListPair = (Natural, Natural)
  type Position ListPair = SumFin

  toContainer (ListPair (xs, ys)) = Extension
    { shape = (genericLength xs, genericLength ys)
    , position = Map.fromList (zip [0..] (xs ++ ys))
    }
  fromContainer (Extension (n, _) p) = ListPair (Map.elems a, Map.elems b)
    where (a, b) = Map.splitAt (fromIntegral n) p

newtype DoubleFin = DoubleFin Natural
  deriving newtype (Eq, Ord, Enum, Show, Num, Encode)

instance Dep DoubleFin where
  type Arg DoubleFin = Natural
  depend n = depend @Fin (2 * n)

-- | A type synonym for @[(a, a)]@ with a container instance
-- \[
-- (n : \textit{Nat}) \triangleright \textit{Fin}\ 2n
-- \]
newtype PairList a = PairList [(a, a)]
  deriving stock (Eq, Ord, Show)
  deriving stock Functor

instance Container PairList where
  type Shape    PairList = Natural
  type Position PairList = DoubleFin

  toContainer (PairList xs) = Extension
    { shape = genericLength xs
    , position = Map.fromList . concatMap (\(i, (x, y)) ->
      [(DoubleFin i, x), (DoubleFin (i + 1), y)]) $ zip [0..] xs
    }
  fromContainer (Extension _ p) = PairList $ pairup $ Map.elems p
    where
      pairup [] = []
      pairup (x:y:ys) = (x, y) : pairup ys
      pairup _ = error "Mismatching pairs"

instance Container Dup where
  type Shape    Dup = ()
  type Position Dup = Const Bool ()

  toContainer (Dup (x, y)) = Extension () $
    Map.fromList [(Const False, x), (Const True, y)]
  fromContainer (Extension _ p) = Dup (p Map.! Const False, p Map.! Const True)
