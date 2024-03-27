module Utils
  ( allSame
  , nonEmpty
  , partitionWith
  ) where

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
