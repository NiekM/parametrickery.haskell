{-# LANGUAGE GHC2021, TypeFamilies, UndecidableInstances #-}

module Container (Container(..), Extension(..)) where

import Data.Kind

import Numeric.Natural

import Map qualified
import Data.Map (Map)
import Data.Map qualified as Map

import Data.List (genericLength)
import Data.Functor.Identity
import Data.Functor.Const
import Data.Functor.Product
import Data.Functor.Sum
import Data.Functor.Compose
import Unsafe

import Data.SBV
import Data.SBV.Tuple qualified as SBV
import Data.SBV.Either qualified as SBV
import Data.Proxy
import Data.Bifunctor

class (Ord (Position f), SymVal (RawShape f), SymVal (RawPosition f))
  => Container (f :: Type -> Type) where
  data Shape f :: Type
  data Position f :: Type

  toContainer :: f a -> Extension f a
  fromContainer :: Extension f a -> f a

  type RawShape f :: Type
  type RawPosition f :: Type

  rawShape :: Shape f -> RawShape f
  rawPosition :: Position f -> RawPosition f

  refine :: Proxy f -> SBV (RawShape f) -> SBool
  refine Proxy _ = sTrue

  depend :: Proxy f -> SBV (RawShape f) -> SBV (RawPosition f) -> SBool
  depend Proxy _ _ = sTrue

data Extension f a = Extension
  { shape :: Shape f
  , position :: Map (Position f) a
  }

deriving instance (Show (Shape f), Show (Position f), Show a) => Show (Extension f a)  

instance Container [] where
  newtype Shape [] = ListShape Natural
    deriving newtype (Eq, Ord, Enum, Num, Real, Integral)
  newtype Position [] = ListPosition Natural
    deriving newtype (Eq, Ord, Enum, Num, Real, Integral)

  toContainer xs = Extension
    { shape = genericLength xs
    , position = Map.fromList (zip [0..] xs)
    }
  fromContainer = Map.elems . position

  type RawShape [] = Integer
  type RawPosition [] = Integer

  rawShape = toInteger
  rawPosition = toInteger

  refine Proxy s = s .>= 0
  depend Proxy s p = p .>= 0 .&& p .< s

instance Container Identity where
  data Shape Identity = IdShape
  data Position Identity = IdPosition
    deriving (Eq, Ord, Show)

  toContainer = Extension IdShape . Map.singleton IdPosition . runIdentity
  fromContainer = Identity . lookupError IdPosition . position

  type RawShape Identity = Integer
  type RawPosition Identity = Integer

  rawShape _ = 0
  rawPosition _ = 0

  refine Proxy s = s .== 0
  depend Proxy _ p = p .== 0

class SymVal (Raw a) => Refined a where
  type Raw a :: Type
  raw :: a -> Raw a
  refineRaw :: Proxy a -> SBV (Raw a) -> SBool

instance Refined () where
  type Raw () = Integer
  raw _ = 0
  refineRaw Proxy n = n .== 0

instance Refined Natural where
  type Raw Natural = Integer
  raw = toInteger
  refineRaw Proxy n = n .>= 0

instance Refined k => Container (Const k) where
  newtype Shape (Const k) = ConstShape { unConstShape :: k }
  data Position (Const k)
    deriving (Eq, Ord)

  toContainer (Const x) = Extension (ConstShape x) mempty
  fromContainer = Const . unConstShape . shape

  type RawShape (Const k) = Raw k
  type RawPosition (Const k) = Integer

  rawShape = raw . unConstShape
  rawPosition _ = 0

  refine Proxy = refineRaw @k Proxy
  depend Proxy _ _ = sFalse

deriving instance (Eq (Position f), Eq (Position g)) => Eq (Position (Product f g))
deriving instance (Ord (Position f), Ord (Position g)) => Ord (Position (Product f g))

instance (Container f, Container g) => Container (Product f g) where
  newtype Shape (Product f g) =
    ProductShape { unProductShape :: (Shape f, Shape g) }
  newtype Position (Product f g) =
    ProductPosition { unProductPosition :: Either (Position f) (Position g)}

  toContainer (Pair x y) = Extension 
    { shape = ProductShape (s, t)
    , position = Map.mapKeysMonotonic ProductPosition
      (Map.mapKeysMonotonic Left p <> Map.mapKeysMonotonic Right q)
    }
    where
      Extension s p = toContainer x
      Extension t q = toContainer y

  fromContainer (Extension (ProductShape (s, t)) pq) = Pair x y
    where
      (p, q) = Map.splitEither $ Map.mapKeysMonotonic unProductPosition pq
      x = fromContainer (Extension s p)
      y = fromContainer (Extension t q)

  type RawShape (Product f g) = (RawShape f, RawShape g)
  type RawPosition (Product f g) = Either (RawPosition f) (RawPosition g)

  rawShape = bimap rawShape rawShape . unProductShape
  rawPosition = bimap rawPosition rawPosition . unProductPosition

  refine Proxy s = let (x, y) = SBV.untuple s in
    refine @f Proxy x .&& refine @g Proxy y

  depend Proxy s = let (x, y) = SBV.untuple s in
    SBV.either (depend @f Proxy x) (depend @g Proxy y)

deriving instance (Eq (Position f), Eq (Position g)) => Eq (Position (Sum f g))
deriving instance (Ord (Position f), Ord (Position g)) => Ord (Position (Sum f g))

instance (Container f, Container g) => Container (Sum f g) where
  newtype Shape (Sum f g) =
    SumShape { unSumShape :: Either (Shape f) (Shape g) }
  newtype Position (Sum f g) =
    SumPosition { unSumPosition :: Either (Position f) (Position g) }

  toContainer (InL x) =
    Extension (SumShape $ Left s) (Map.mapKeysMonotonic (SumPosition . Left) p)
    where Extension s p = toContainer x
  toContainer (InR y) =
    Extension (SumShape $ Right t) (Map.mapKeysMonotonic (SumPosition . Right) q)
    where Extension t q = toContainer y

  fromContainer = \case
    Extension (SumShape (Left s)) p -> InL $ fromContainer $ Extension s p'
      where p' = Map.mapKeysMonotonic (stripLeft . unSumPosition) p
    Extension (SumShape (Right t)) q -> InR $ fromContainer $ Extension t q'
      where q' = Map.mapKeysMonotonic (stripRight . unSumPosition) q

  type RawShape (Sum f g) = Either (RawShape f) (RawShape g)
  type RawPosition (Sum f g) = Either (RawPosition f) (RawPosition g)

  rawShape = bimap rawShape rawShape . unSumShape
  rawPosition = bimap rawPosition rawPosition . unSumPosition

  -- TODO: check if these are actually correct
  refine Proxy = SBV.either (refine @f Proxy) (refine @g Proxy)
  depend Proxy s p = SBV.either
    (\l -> SBV.either (depend @f Proxy l) (const sFalse) p)
    (\r -> SBV.either (const sFalse) (depend @g Proxy r) p)
    s

-- deriving instance (Eq (Position f), Eq (Position g)) => Eq (Position (Compose f g))
-- deriving instance (Ord (Position f), Ord (Position g)) => Ord (Position (Compose f g))

-- instance (Container f, Container g) => Container (Compose f g) where
--   newtype Shape (Compose f g) = ComposeShape (Extension f (Shape g))
--   newtype Position (Compose f g) =
--     ComposePosition { unComposePosition :: (Position f, Position g)}

--   toContainer (Compose x) =
--     let
--       Extension s p = toContainer x
--       m = fmap toContainer p
--       s' = fmap shape m
--       p' = fmap position m
--     in Extension
--       (ComposeShape $ Extension s s')
--       (Map.mapKeysMonotonic ComposePosition $ Map.uncurry p')

--   fromContainer (Extension (ComposeShape (Extension s s')) q) =
--     let
--       p' = Map.curry $ Map.mapKeysMonotonic unComposePosition q
--       m = Map.merge (Map.mapMissing (\_ t -> Extension t mempty))
--         Map.dropMissing
--         (Map.zipWithMatched $ const Extension) s' p'
--       x = fromContainer $ Extension s (fmap fromContainer m)
--     in Compose x

--   -- The list of (RawPosition f, RawShape g) represents the outputs (in order)
--   -- of the position function from RawPosition f to RawShape g.
--   type RawShape (Compose f g) = (RawShape f, [(RawPosition f, RawShape g)])
--   type RawPosition (Compose f g) = (RawPosition f, RawPosition g)

--   rawShape (ComposeShape (Extension s p)) =
--     (rawShape s, bimap rawPosition rawShape <$> Map.assocs p)
--   rawPosition = bimap rawPosition rawPosition . unComposePosition

--   refine Proxy s = let (x, y) = SBV.untuple s in
--     refine @f Proxy x .&& _ ???
--   depend Proxy s p = _ ???