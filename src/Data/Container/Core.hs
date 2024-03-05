{-# LANGUAGE UndecidableInstances #-}

module Data.Container.Core (Container(..), Extension(..)) where

import Data.Map qualified as Map
import Data.List (genericLength)
import Data.Maybe (isJust)

import Data.SBV
import Data.SBV.Tuple  qualified as SBV
import Data.SBV.Either qualified as SBV

import Base
import Dependent
import Map qualified
import Unsafe qualified

type Dependent a b = (Ref a, Dep b, Arg b ~ a)

class (Dependent (Shape f) (Position f), Ord (Position f))
  => Container (f :: Type -> Type) where
  type Shape    f :: Type
  type Position f :: Type

  toContainer   :: f a -> Extension f a
  fromContainer :: Extension f a -> f a

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
  type Position Identity = K () ()

  toContainer = Extension () . Map.singleton (K ()) . runIdentity
  fromContainer = Identity . Unsafe.lookupError (K ()) . position

-- | Const

instance Ref k => Container (Const k) where
  type Shape    (Const k) = k
  type Position (Const k) = K k Void

  toContainer (Const x) = Extension x mempty
  fromContainer = Const . shape

-- | Product

newtype OR a b = OR (Either a b)
  deriving newtype (Eq, Ord, Show, Encode)

instance (Dep a, Dep b) => (Dep (OR a b)) where
  type Arg (OR a b) = (Arg a, Arg b)
  dep Proxy t = SBV.either (dep @a Proxy x) (dep @b Proxy y)
    where (x, y) = SBV.untuple t

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

newtype XOR a b = XOR { unXOR :: Either a b }
  deriving newtype (Eq, Ord, Show, Encode)

instance (Dep a, Dep b) => (Dep (XOR a b)) where
  type Arg (XOR a b) = Either (Arg a) (Arg b)
  dep Proxy e d =
    SBV.either
    (\l -> SBV.isLeft  d .&& dep @a Proxy l (SBV.fromLeft  d))
    (\r -> SBV.isRight d .&& dep @b Proxy r (SBV.fromRight d))
    e

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
    Extension (Left s) p -> InL $ fromContainer $ Extension s $
      Map.mapKeysMonotonic (Unsafe.stripLeft . unXOR) p
    Extension (Right t) q -> InR $ fromContainer $ Extension t $
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

newtype May = May ()
  deriving stock (Eq, Ord, Show)
  deriving newtype Encode

instance Dep May where
  type Arg May = Bool
  dep Proxy m _ = m .== sTrue

instance Container Maybe where
  type Shape    Maybe = Bool
  type Position Maybe = May

  toContainer x = Extension
    { shape = isJust x
    , position = maybe Map.empty (Map.singleton (May ())) x
    }
  fromContainer = Map.lookup (May ()) . position
