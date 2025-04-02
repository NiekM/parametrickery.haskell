{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Control.Effect.Search
  ( WeightedSearch
  , module Control.Effect.Weight
  , module Control.Effect.Choose
  , limit
  ) where

import Control.Monad.Search

import Control.Algebra
import Control.Effect.Choose
import Control.Effect.Weight

import Base hiding ((<|>))

type WeightedSearch = Choose :+: Weight

instance Algebra WeightedSearch (Search (Sum Nat)) where
  alg _ sig ctx = case sig of
    L Choose ->
      let l = False <$ ctx; r = True <$ ctx in junction (pure l) (pure r)
    R (Weigh w) -> ctx <$ cost' (Sum w)

limit :: (Has WeightedSearch sig m) => Nat -> m a -> m (Maybe a)
limit n m = fmap Just m <|> (weigh (n + 1) >> foldr1 (<|>) (repeat $ pure Nothing))
