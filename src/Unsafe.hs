{- |
Module      : Unsafe
Copyright   : (c) Anonymous 2024
Maintainer  : Anonymous

Some unsafe helper functions.

-}
module Unsafe
  ( lookupError
  , stripLeft
  , stripRight
  , coerceKeys
  ) where

import Data.Map (Map)
import Data.Map qualified as Map
import Data.Coerce (Coercible)
import Unsafe.Coerce (unsafeCoerce)
import GHC.Stack (HasCallStack)

-- | Look up a key @k@ in a 'Data.Map.Map', returning an error if the key is
-- missing.
--
-- WARNING: This function is partial. Consider using 'Data.Map.lookup' instead.
--
lookupError :: (HasCallStack, Ord k, Show k) => k -> Map k v -> v
lookupError k m = case Map.lookup k m of
  Nothing -> error $ "Missing element at position " <> show k
  Just v -> v

-- | Take the left value out of an 'Data.Either.Either'.
--
-- WARNING: This function is partial. Consider pattern matching instead.
--
stripLeft :: HasCallStack => Either a b -> a
stripLeft (Left x) = x
stripLeft _ = error "Expected Left"

-- | Take the right value out of an 'Data.Either.Either'.
--
-- WARNING: This function is partial. Consider pattern matching instead.
--
stripRight :: HasCallStack => Either a b -> b
stripRight (Right y) = y
stripRight _ = error "Expected Right"

-- | Convert between 'Data.Map.Map's with keys that have the same representation
-- with no run-time overhead.

-- Note that the 'Coercible' constraint is not necessary, but it ensures that
-- we can only apply it in sensible situations. I'm relatively sure that this
-- makes 'coerceKeysMonotonic' safe.
coerceKeys :: Coercible k1 k2 => Map k1 v -> Map k2 v
coerceKeys = unsafeCoerce
