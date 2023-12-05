module Container (Container(..), Extension(..)) where

import Data.Kind

import Numeric.Natural

import Map qualified
import Data.Map (Map)
import Data.Map qualified as Map

import Data.List (genericLength)
import Data.Void
import Data.Functor.Identity
import Data.Functor.Const
import Data.Functor.Product
import Data.Functor.Sum
import Unsafe qualified

import Dependent

class (Ref (Shape f), Dep (Position f), Arg (Position f) ~ Shape f, Ord (Position f))
  => Container (f :: Type -> Type) where
  type Shape f :: Type
  type Position f :: Type

  toContainer :: f a -> Extension f a
  fromContainer :: Extension f a -> f a

data Extension f a = Extension
  { shape :: Shape f
  , position :: Map (Position f) a
  }

deriving instance (Show (Shape f), Show (Position f), Show a) => Show (Extension f a)

-- | Container instances

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
  type Position Identity = K () ()

  toContainer = Extension () . Map.singleton (K ()) . runIdentity
  fromContainer = Identity . Unsafe.lookupError (K ()) . position

instance Ref k => Container (Const k) where
  type Shape (Const k) = k
  type Position (Const k) = K k Void

  toContainer (Const x) = Extension x mempty
  fromContainer = Const . shape

instance (Container f, Container g) => Container (Product f g) where
  type Shape (Product f g) = (Shape f, Shape g)
  type Position (Product f g) = OR (Position f) (Position g)

  toContainer (Pair x y) = Extension
    { shape = (s, t)
    , position = Unsafe.coerceKeysMonotonic $
      Map.mapKeysMonotonic Left p <> Map.mapKeysMonotonic Right q
    } where
      Extension s p = toContainer x
      Extension t q = toContainer y
  fromContainer (Extension (s, t) pq) = Pair x y
    where
      (p, q) = Map.splitEither $ Unsafe.coerceKeysMonotonic pq
      x = fromContainer (Extension s p)
      y = fromContainer (Extension t q)

instance (Container f, Container g) => Container (Sum f g) where
  type Shape (Sum f g) = Either (Shape f) (Shape g)
  type Position (Sum f g) = XOR (Position f) (Position g)

  toContainer = \case
    InL x ->
      let Extension s p = toContainer x
      in Extension (Left s) (Map.mapKeysMonotonic (XOR . Left) p)
    InR y ->
      let Extension t q = toContainer y
      in Extension (Right t) (Map.mapKeysMonotonic (XOR . Right) q)
  fromContainer = \case
    Extension (Left s) p -> InL $ fromContainer $ Extension s $
      Map.mapKeysMonotonic (Unsafe.stripLeft . unXOR) p
    Extension (Right t) q -> InR $ fromContainer $ Extension t $
      Map.mapKeysMonotonic (Unsafe.stripRight . unXOR) q