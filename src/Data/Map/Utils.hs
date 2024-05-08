module Data.Map.Utils (splitEither) where

import Prelude hiding (uncurry, curry)

import Data.Map.Internal
import Utils.Containers.Internal.StrictPair

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
