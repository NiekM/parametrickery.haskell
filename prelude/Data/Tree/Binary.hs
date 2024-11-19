module Data.Tree.Binary where

import Base
import GHC.Generics
import Test.QuickCheck

data Tree a b
  = Leaf b
  | Node (Tree a b) a (Tree a b)
  deriving (Eq, Ord, Show, Generic)

foldTree :: (c -> a -> c -> c) -> (b -> c) -> Tree a b -> c
foldTree node leaf = \case
  Leaf x -> leaf x
  Node l x r -> node (foldTree node leaf l) x (foldTree node leaf r)

instance Arbitrary2 Tree where
  liftArbitrary2 gen1 gen2 = sized \n -> do
    k <- choose (0, n)
    go k
    where
      go 0 = Leaf <$> gen2
      go n = do
        k <- choose (0, n - 1)
        Node <$> go k <*> gen1 <*> go (n - k - 1)

instance (Arbitrary a, Arbitrary b) => Arbitrary (Tree a b) where
  arbitrary = arbitrary2
