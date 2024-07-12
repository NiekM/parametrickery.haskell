module Data.Map.Multi
  ( Multi
  , singleton
  , union, intersection
  , lookup
  , fromMap, toMap
  , elems
  , map
  , compose
  , inverse
  , remapping
  , consistent
  , filterWithKey
  ) where

import Prelude hiding (map, lookup)
import Data.Map qualified as Map
import Data.Map.Utils qualified as Map
import Data.Set qualified as Set
import Data.Coerce

import Base

-- TODO: would nonempty sets make more sense?
newtype Multi k v = Multi { getMulti :: Map k (Set v) }
  deriving newtype (Eq, Ord, Show, Read)

singleton :: k -> v -> Multi k v
singleton k = Multi . Map.singleton k . Set.singleton

fromMap :: Map k v -> Multi k v
fromMap = coerce $ Map.map Set.singleton

toMap :: Multi k v -> Maybe (Map k v)
toMap = traverse Set.lookupMin . getMulti

elems :: Multi k v -> [Set v]
elems = Map.elems . getMulti

union :: (Ord k, Ord v) => Multi k v -> Multi k v -> Multi k v
union = coerce $ Map.unionWith Set.union

-- TODO: does this make sense?
intersection :: (Ord k, Ord v) => Multi k v -> Multi k v -> Multi k v
intersection = coerce $ Map.intersectionWith Set.intersection

lookup :: (Ord k, Ord v) => k -> Multi k v -> Set v
lookup k = coerce $ Map.lookupDefault k Set.empty

map :: Ord b => (a -> b) -> Multi k a -> Multi k b
map = coerce . Map.map . Set.map

mapMany :: Ord b => (a -> Set b) -> Multi k a -> Multi k b
mapMany = coerce . Map.map . foldMap @Set

inverse :: (Ord k, Ord v) => Multi k v -> Multi v k
inverse = coerce
  $ Map.unionsWith Set.union
  . fmap (\(k, vs) -> Map.fromSet (const $ Set.singleton k) vs)
  . Map.toList

compose :: (Ord b, Ord c) => Multi b c -> Multi a b -> Multi a c 
compose = mapMany . flip lookup

remapping :: (Ord k2, Ord v) => Multi k1 v -> Multi k2 v -> Multi k1 k2
remapping m = flip compose m . inverse

consistent :: Multi k v -> Maybe (Multi k v)
consistent (Multi m)
  | not (any Set.null m) = Just (Multi m)
  | otherwise = Nothing

filterWithKey :: (k -> v -> Bool) -> Multi k v -> Multi k v
filterWithKey f = coerce $ Map.mapWithKey \k v -> Set.filter (f k) v
