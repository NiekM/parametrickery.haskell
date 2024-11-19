{-# LANGUAGE UndecidableInstances #-}

module Test.Compare where

import Test.QuickCheck

class Compare a where
  comparison :: a -> a -> Property

instance {-# OVERLAPPABLE #-} Eq a => Compare a where
  comparison x y = property $ x == y

instance {-# OVERLAPPABLE #-} (Arbitrary a, Show a, Compare b) =>
  Compare (a -> b) where
  comparison f g = property \x -> comparison (f x) (g x)
