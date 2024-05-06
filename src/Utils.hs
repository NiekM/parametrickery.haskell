module Utils
  ( allSame
  , nonEmpty
  , partitionWith
  , maybeToEither
  , mapEither
  , extract
  ) where

import Data.Map.Strict qualified as Map

import Base

allSame :: Eq a => NonEmpty a -> Maybe a
allSame (x :| xs)
  | all (== x) xs = Just x
  | otherwise     = Nothing

nonEmpty :: Set a -> Maybe (Set a)
nonEmpty x
  | null x    = Nothing
  | otherwise = Just x

partitionWith :: (a -> Either b c) -> [a] -> ([b], [c])
partitionWith f = ([], []) & foldr \x -> case f x of
  Left  a -> first  (a:)
  Right b -> second (b:)

maybeToEither :: e -> Maybe a -> Either e a
maybeToEither e = maybe (Left e) Right

mapEither :: (a -> Either b c) -> [a] -> ([b], [c])
mapEither f = partitionEithers . fmap f

extract :: (Traversable f, Ord a) => f (a, b) -> (Map a b, f a)
extract = traverse \(x, y) -> (Map.singleton x y, x)
