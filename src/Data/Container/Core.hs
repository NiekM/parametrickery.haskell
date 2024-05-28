{-# LANGUAGE UndecidableInstances #-}

{- |
Module      : Data.Container.Core
Copyright   : (c) Niek Mulleners 2024
Maintainer  : n.mulleners@uu.nl

Container functors and their extensions.

-}
module Data.Container.Core
  ( Container(..)
  , Extension(..)
  ) where

import Data.Map qualified as Map
import Data.List (genericLength)
import Data.Maybe (isJust)

import Data.SBV.Depend

import Base
import Data.Map.Utils qualified as Map
import Unsafe qualified

type Dependent a b = (Ref a, Dep b, Arg b ~ a)

-- | A type @f@ is a Container if there is an isomorphism between @f@ and its
-- container extension, defined by the 'Shape' and 'Position' type families.
--
-- [Left-Inverse]  @'toContainer' . 'fromContainer' == 'id'@
-- [Right-Inverse] @'fromContainer' . 'toContainer' == 'id'@
--
class (Dependent (Shape f) (Position f), Ord (Position f))
  => Container (f :: Type -> Type) where
  type Shape    f :: Type
  type Position f :: Type

  toContainer   :: f a -> Extension f a
  fromContainer :: Extension f a -> f a

-- | The extension of a container functor
data Extension f a = Extension
  { shape    :: Shape f
  , position :: Map (Position f) a
  } deriving stock Functor

type Each :: (Type -> Constraint) -> (Type -> Type) -> Type -> Constraint
type Each c f a = (c (Shape f), c (Position f), c a)

deriving instance Each Eq   f a => Eq   (Extension f a)
deriving instance Each Ord  f a => Ord  (Extension f a)
deriving instance Each Show f a => Show (Extension f a)

-- | Identity

instance Container Identity where
  type Shape    Identity = ()
  type Position Identity = Const () ()

  toContainer = Extension () . Map.singleton (Const ()) . runIdentity
  fromContainer = Identity . Unsafe.lookupError (Const ()) . position

-- | Const

instance Ref k => Container (Const k) where
  type Shape    (Const k) = k
  type Position (Const k) = Const Void k

  toContainer (Const x) = Extension x mempty
  fromContainer = Const . shape

-- | Product

instance (Container f, Container g) => Container (Product f g) where
  type Shape    (Product f g) = (Shape f, Shape g)
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

-- | Sum

instance (Container f, Container g) => Container (Sum f g) where
  type Shape    (Sum f g) = Either (Shape f) (Shape g)
  type Position (Sum f g) = XOR (Position f) (Position g)

  toContainer = \case
    InL x ->
      let Extension s p = toContainer x
      in Extension (Left s) (Map.mapKeysMonotonic (XOR . Left) p)
    InR y ->
      let Extension t q = toContainer y
      in Extension (Right t) (Map.mapKeysMonotonic (XOR . Right) q)
  fromContainer = \case
    Extension (Left  s) p -> InL . fromContainer . Extension s $
      Map.mapKeysMonotonic (Unsafe.stripLeft . unXOR) p
    Extension (Right t) q -> InR . fromContainer . Extension t $
      Map.mapKeysMonotonic (Unsafe.stripRight . unXOR) q

-- | List

instance Container [] where
  type Shape    [] = Natural
  type Position [] = Fin

  toContainer xs = Extension
    { shape = genericLength xs
    , position = Map.fromList $ zip [0..] xs
    }
  fromContainer = Map.elems . position

-- | Maybe

instance Container Maybe where
  type Shape    Maybe = Bool
  type Position Maybe = May

  toContainer x = Extension
    { shape = isJust x
    , position = maybe Map.empty (Map.singleton (May ())) x
    }
  fromContainer = Map.lookup (May ()) . position
