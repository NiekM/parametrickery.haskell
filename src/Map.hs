module Map (splitEither, uncurry, curry) where

import Prelude hiding (uncurry, curry)

import Data.Map
import Data.Map.Internal
import Utils.Containers.Internal.StrictPair

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

-- Why does this not work? :(
-- You would think that Map k1 v and Map k2 v have the same runtime representation.
-- I guess this relies on the Ord constraints of k1 and k2, which should be equivalent.
-- It would be nice if we could benefit from knowing they are the same.
-- coerceKeysMonotonic :: Coercible k1 k2 => Map k1 v -> Map k2 v
-- coerceKeysMonotonic = coerce