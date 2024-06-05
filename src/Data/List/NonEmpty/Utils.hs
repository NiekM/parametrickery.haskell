module Data.List.NonEmpty.Utils where

import Data.List.NonEmpty

snoc :: [a] -> a -> NonEmpty a
snoc xs x = foldr cons (pure x) xs
