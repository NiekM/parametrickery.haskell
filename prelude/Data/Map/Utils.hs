module Data.Map.Utils
  ( lookupDefault
  , inverse
  ) where

import Prelude hiding (uncurry, curry)

import Data.Maybe (fromMaybe)
import Data.Map as Map
import Data.Set (Set)
import Data.Set qualified as Set

lookupDefault :: Ord k => k -> v -> Map k v -> v
lookupDefault k d = fromMaybe d . Map.lookup k

inverse :: (Ord k, Ord v) => Map k v -> Map v (Set k)
inverse = unionsWith (<>)
  . fmap (\(k, v) -> Map.singleton v (Set.singleton k))
  . Map.toList
