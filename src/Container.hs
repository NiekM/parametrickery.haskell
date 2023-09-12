{-# LANGUAGE GHC2021, TypeFamilies, UndecidableInstances #-}

module Container (Container(..), Extension(..)) where

import Data.Kind

import Numeric.Natural

import Map qualified
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Map.Internal qualified as Map

import Data.Void
import Data.List (genericLength)
import Data.Functor.Identity
import Data.Functor.Const
import Data.Functor.Product
import Data.Functor.Sum
import Data.Functor.Compose
import Unsafe
import Types

class Ord (Position f) => Container (f :: Type -> Type) where
  type Shape f :: Type
  type Position f :: Type

  toContainer :: f a -> Extension f a
  fromContainer :: Extension f a -> f a

data Extension f a = Extension
  { shape :: Shape f
  , position :: Map (Position f) a
  }

deriving instance (Show (Shape f), Show (Position f), Show a) => Show (Extension f a)  

instance Container [] where
  type Shape [] = Natural
  type Position [] = Fin

  toContainer xs = Extension
    { shape = genericLength xs
    , position = Map.fromList (zip [0..] xs)
    }
  fromContainer = Map.elems . position

instance Container Identity where
  type Shape Identity = ()
  type Position Identity = K ()

  toContainer = Extension () . Map.singleton (K ()) . runIdentity
  fromContainer = Identity . lookupError (K ()) . position

instance Container (Const k) where
  type Shape (Const k) = k
  type Position (Const k) = K Void

  toContainer (Const x) = Extension x mempty
  fromContainer = Const . shape

instance (Container f, Container g) => Container (Product f g) where
  type Shape (Product f g) = (Shape f, Shape g)
  type Position (Product f g) = Either (Position f) (Position g)

  toContainer (Pair x y) = Extension 
    { shape = (s, t)
    , position = Map.mapKeysMonotonic Left p <> Map.mapKeysMonotonic Right q
    }
    where
      Extension s p = toContainer x
      Extension t q = toContainer y

  fromContainer (Extension (s, t) pq) = Pair x y
    where
      (p, q) = Map.splitEither pq
      x = fromContainer (Extension s p)
      y = fromContainer (Extension t q)

instance (Container f, Container g) => Container (Sum f g) where
  type Shape (Sum f g) = Either (Shape f) (Shape g)
  type Position (Sum f g) = Either (Position f) (Position g)

  toContainer (InL x) = Extension (Left s) (Map.mapKeysMonotonic Left p)
    where Extension s p = toContainer x
  toContainer (InR y) = Extension (Right t) (Map.mapKeysMonotonic Right q)
    where Extension t q = toContainer y

  fromContainer = \case
    Extension (Left s) p -> InL $ fromContainer $ Extension s p'
      where p' = Map.mapKeysMonotonic stripLeft p
    Extension (Right t) q -> InR $ fromContainer $ Extension t q'
      where q' = Map.mapKeysMonotonic stripRight q

instance (Container f, Container g) => Container (Compose f g) where
  type Shape (Compose f g) = Extension f (Shape g)
  type Position (Compose f g) = (Position f, Position g)

  toContainer (Compose x) =
    let
      Extension s p = toContainer x
      m = fmap toContainer p
      s' = fmap shape m
      p' = fmap position m
    in Extension (Extension s s') (Map.uncurry p')

  fromContainer (Extension (Extension s s') q) =
    let
      p' = Map.curry q
      m = Map.merge (Map.mapMissing (\_ t -> Extension t mempty))
        Map.dropMissing
        (Map.zipWithMatched $ const Extension) s' p'
      x = fromContainer $ Extension s (fmap fromContainer m)
    in Compose x