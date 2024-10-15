module Utils
  ( altMap
  , mapEither
  , extract, inject
  , ordered
  ) where

import Data.Map.Strict qualified as Map
import Control.Applicative
import Data.Monoid (Alt(..))

import Base

altMap :: (Foldable f, Alternative m) => (a -> m b) -> f a -> m b
altMap f = getAlt . foldMap (Alt . f)

mapEither :: (a -> Either b c) -> [a] -> ([b], [c])
mapEither f = partitionEithers . fmap f

extract :: (Traversable f, Ord k) => f (k, v) -> (f k, Map k v)
extract = swap . traverse \(x, y) -> (Map.singleton x y, x)

inject :: (Traversable f, Ord k) => Map k v -> f k -> Maybe (f v)
inject m = traverse (`Map.lookup` m)

ordered :: Ord a => [a] -> Bool
ordered [] = True
ordered (x:xs) = and $ zipWith (<=) (x:xs) xs
