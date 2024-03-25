module Data.Map.Utils
  ( splitEither
  , uncurry, curry
  , lookupDefault
  , unionsWithA
  , fromListWith'
  , mapKeysMaybe
  , inverse
  ) where

import Prelude hiding (uncurry, curry)

import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (fromMaybe, isJust)
import Data.Map as Map
import Data.Map.Internal
import Data.Set (Set)
import Data.Set qualified as Set
import Utils.Containers.Internal.StrictPair

import Unsafe qualified

_mapEitherWithKey :: (k -> a -> Either b c) -> Map k a -> (Map k b, Map k c)
_mapEitherWithKey f0 t0 = toPair $ go f0 t0
  where
    go _ Tip = Tip :*: Tip
    go f (Bin _ kx x l r) = case f kx x of
      Left y  -> y `seq` (link kx y l1 r1 :*: link2 l2 r2)
      Right z -> z `seq` (link2 l1 r1 :*: link kx z l2 r2)
      where
        (l1 :*: l2) = go f l
        (r1 :*: r2) = go f r

splitEither :: Map (Either k1 k2) a -> (Map k1 a, Map k2 a)
splitEither t0 = toPair $ go t0
  where
    go Tip = Tip :*: Tip
    go (Bin _ kx x l r) = case kx of
      Left  k0 -> k0 `seq` (link k0 x l1 r1 :*: link2 l2 r2)
      Right k1 -> k1 `seq` (link2 l1 r1 :*: link k1 x l2 r2)
      where
        (l1 :*: l2) = go l
        (r1 :*: r2) = go r

uncurry :: (Ord k1, Ord k2) => Map k1 (Map k2 v) -> Map (k1, k2) v
uncurry = unions . mapWithKey \k -> mapKeysMonotonic (k,)

curry :: (Ord k1, Ord k2) => Map (k1, k2) v -> Map k1 (Map k2 v)
curry = mapKeysWith union fst . mapWithKey \(_, k) -> singleton k

unionsWithA :: (Applicative m, Functor f, Foldable f, Ord k) =>
  (NonEmpty a -> m b) -> f (Map k a) -> m (Map k b)
unionsWithA f = traverse f . unionsWith (<>) . fmap (fmap pure)

fromListWith' :: Ord k => (NonEmpty a -> b) -> [(k, a)] -> Map k b
fromListWith' f = fmap f . unionsWith (<>)
  . fmap \(k, v) -> singleton k (pure v)

lookupDefault :: Ord k => k -> v -> Map k v -> v
lookupDefault k d = fromMaybe d . Map.lookup k

mapKeysMaybe :: Ord k2 => (k1 -> Maybe k2) -> Map k1 v -> Map k2 v
mapKeysMaybe f = mapKeysMonotonic Unsafe.stripJust
  . filterWithKey (\k _ -> isJust k) . mapKeys f

inverse :: (Ord k, Ord v) => Map k v -> Map v (Set k)
inverse = unionsWith (<>)
  . fmap (\(k, v) -> Map.singleton v (Set.singleton k))
  . Map.toList
