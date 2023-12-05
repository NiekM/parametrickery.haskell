module Unsafe (lookupError, stripLeft, stripRight, coerceKeysMonotonic) where

import Data.Map (Map)
import Data.Map qualified as Map
import Unsafe.Coerce

lookupError :: (Ord k, Show k) => k -> Map k v -> v
lookupError k m = case Map.lookup k m of
  Nothing -> error $ "Missing element at position " <> show k
  Just v -> v

stripLeft :: Either a b -> a
stripLeft (Left x) = x
stripLeft _ = error "Expected Left"

stripRight :: Either a b -> b
stripRight (Right y) = y
stripRight _ = error "Expected Right"

coerceKeysMonotonic :: Map k1 v -> Map k2 v
coerceKeysMonotonic = unsafeCoerce