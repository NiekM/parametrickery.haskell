module Data.Map.Multi
  ( Multi
  , empty
  , singleton
  , union, unions
  , intersection, intersectionWith
  , lookup
  , fromMap, toMap
  , keys, elems
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
newtype Multi k v = Multi (Map k (Set v))
  deriving newtype (Eq, Ord, Show, Read)

empty :: Multi k v
empty = Multi Map.empty

singleton :: k -> v -> Multi k v
singleton k = Multi . Map.singleton k . Set.singleton

fromMap :: Map k v -> Multi k v
fromMap = coerce $ Map.map Set.singleton

toMap :: Multi k v -> Maybe (Map k v)
toMap = coerce $ traverse @(Map _) Set.lookupMin

keys :: Multi k v -> Set k
keys = coerce $ Map.keysSet @_ @(Set _)

elems :: Multi k v -> [Set v]
elems = coerce $ Map.elems @_ @(Set _)

union :: (Ord k, Ord v) => Multi k v -> Multi k v -> Multi k v
union = coerce $ Map.unionWith Set.union

unions :: (Ord k, Ord v) => [Multi k v] -> Multi k v
unions = coerce $ Map.unionsWith @[] Set.union

intersection :: (Ord k, Ord v) => Multi k v -> Multi k v -> Multi k v
intersection = coerce $ Map.intersectionWith Set.intersection

intersectionWith :: (Ord k, Ord v, Ord w) =>
  (Set v -> Set v -> Set w) -> Multi k v -> Multi k v -> Multi k w
intersectionWith f = coerce $ Map.intersectionWith f

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

consistent :: Multi k v -> Bool
consistent (Multi m) = not (any Set.null m)

filterWithKey :: (k -> v -> Bool) -> Multi k v -> Multi k v
filterWithKey f = coerce . Map.mapWithKey $ Set.filter . f
