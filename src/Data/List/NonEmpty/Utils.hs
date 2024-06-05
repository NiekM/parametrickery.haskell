{- |
Module      : Data.List.NonEmpty.Utils
Copyright   : (c) Niek Mulleners 2024
Maintainer  : n.mulleners@uu.nl

Some utility functions for 'Data.List.NonEmpty'.

-}
module Data.List.NonEmpty.Utils where

import Data.List.NonEmpty hiding (length)

-- | Prepend an element to a list, resulting in a nonempty list.
snoc :: [a] -> a -> NonEmpty a
snoc xs x = foldr cons (singleton x) xs

-- | Check if all values in a nonempty list are equal.
allSame :: Eq a => NonEmpty a -> Maybe a
allSame (x :| xs)
  | all (x==) xs = Just x
  | otherwise    = Nothing

-- | Compute the average of a nonempty list of values.
average :: Fractional a => NonEmpty a -> a
average xs = sum xs / fromIntegral (length xs)
