{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Control.Effect.Search where

-- import Data.Monoid
-- import Control.Monad.Fail as Fail
-- import Control.Monad.Fix
-- import Control.Monad.IO.Class
-- import Data.Kind
import Control.Monad.Search

import Control.Algebra
import Control.Effect.NonDet
import Control.Effect.Weight

-- import Data.PQueue.Prio.Min

import Base

type WeightedSearch = NonDet :+: Weight

instance Algebra WeightedSearch (Search (Sum Nat)) where
  alg _ sig ctx = case sig of
    L (L Empty) -> abandon
    L (R Choose) ->
      let l = False <$ ctx; r = True <$ ctx in junction (pure l) (pure r)
    R (Weigh w) -> ctx <$ cost' (Sum w)

-- TODO: interpret into some weighted search monad
