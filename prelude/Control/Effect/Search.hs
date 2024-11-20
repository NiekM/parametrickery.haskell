{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Control.Effect.Search
  ( WeightedSearch
  , module Control.Effect.Weight
  , module Control.Effect.NonDet
  , limit
  ) where

import Control.Monad.Search

import Control.Algebra
import Control.Effect.NonDet
import Control.Effect.Weight

import Base

type WeightedSearch = NonDet :+: Weight

instance Algebra WeightedSearch (Search (Sum Nat)) where
  alg _ sig ctx = case sig of
    L (L Empty) -> abandon
    L (R Choose) ->
      let l = False <$ ctx; r = True <$ ctx in junction (pure l) (pure r)
    R (Weigh w) -> ctx <$ cost' (Sum w)

limit :: (Alternative m, Has WeightedSearch sig m) => Nat -> m a -> m (Maybe a)
limit n m = fmap Just m <|> (weigh (n + 1) >> oneOf (repeat Nothing))
