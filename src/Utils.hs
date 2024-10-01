module Utils
  ( altMap
  , allSame
  , nonEmpty
  , partitionWith
  , mapEither
  , extract, inject
  ) where

import Data.Map.Strict qualified as Map
import Control.Applicative
import Data.Monoid (Alt(..))

import Base

altMap :: (Foldable f, Alternative m) => (a -> m b) -> f a -> m b
altMap f = getAlt . foldMap (Alt . f)

allSame :: Eq a => NonEmpty a -> Bool
allSame (x :| xs) = all (== x) xs

nonEmpty :: Set a -> Maybe (Set a)
nonEmpty x
  | null x    = Nothing
  | otherwise = Just x

partitionWith :: (a -> Either b c) -> [a] -> ([b], [c])
partitionWith f = ([], []) & foldr \x -> case f x of
  Left  a -> first  (a:)
  Right b -> second (b:)

mapEither :: (a -> Either b c) -> [a] -> ([b], [c])
mapEither f = partitionEithers . fmap f

extract :: (Traversable f, Ord k) => f (k, v) -> (f k, Map k v)
extract = swap . traverse \(x, y) -> (Map.singleton x y, x)

inject :: (Traversable f, Ord k) => Map k v -> f k -> Maybe (f v)
inject m = traverse (`Map.lookup` m)
