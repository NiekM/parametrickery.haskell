module Data.Tree where

import GHC.Generics

data Tree a b
  = Leaf b
  | Node (Tree a b) a (Tree a b)
  deriving (Eq, Ord, Show, Generic)

foldTree :: (c -> a -> c -> c) -> (b -> c) -> Tree a b -> c
foldTree node leaf = \case
  Leaf x -> leaf x
  Node l x r -> node (foldTree node leaf l) x (foldTree node leaf r)
