{-# LANGUAGE UndecidableInstances #-}

module Data.Container.Specialized
  ( OptList(..)
  , ListPair(..)
  , PairList(..)
  , Dup(..)
  )
  where

import Data.Map qualified as Map
import Data.List (genericLength)
import Data.Proxy (Proxy(..))
import Numeric.Natural (Natural)

import Data.SBV.Tuple qualified as SBV

import Data.Container.Core
import Data.SBV.Encode
import Data.SBV.Depend

-- | OptList

newtype DecFin = DecFin Natural
  deriving newtype (Eq, Ord, Enum, Num, Show, Encode)

instance Dep DecFin where
  type Arg DecFin = Natural
  dep Proxy n = dep @Fin Proxy (n - 1)

newtype OptList a = OptList (Maybe [a])
  deriving stock (Eq, Ord, Show)
  deriving stock Functor

instance Container OptList where
  type Shape    OptList = Natural
  type Position OptList = DecFin

  toContainer (OptList Nothing) = Extension 0 mempty
  toContainer (OptList (Just xs)) = Extension
    { shape = genericLength xs
    , position = Map.fromList (zip [0..] xs)
    }
  fromContainer (Extension 0 _) = OptList Nothing
  fromContainer (Extension _ p) = OptList . Just $ Map.elems p

-- | ListPair

newtype SumFin = FinPair Natural
  deriving newtype (Eq, Ord, Enum, Show, Num, Encode)

instance Dep SumFin where
  type Arg SumFin = (Natural, Natural)
  dep Proxy n = dep @Fin Proxy (a + b)
    where (a, b) = SBV.untuple n

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

-- | PairList

newtype DoubleFin = DoubleFin Natural
  deriving newtype (Eq, Ord, Enum, Show, Num, Encode)

instance Dep DoubleFin where
  type Arg DoubleFin = Natural
  dep Proxy n = dep @Fin Proxy (2 * n)

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

-- | Dup

newtype Dup a = Dup { unDup :: (a, a) }
  deriving newtype (Eq, Ord)
  deriving stock (Show, Functor)

instance Container Dup where
  type Shape    Dup = ()
  type Position Dup = Bool

  toContainer (Dup (x, y)) = Extension () $ Map.fromList [(False, x), (True, y)]
  fromContainer (Extension _ p) = Dup (p Map.! False, p Map.! True)
