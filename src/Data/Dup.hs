module Data.Dup where

import Base

newtype Dup a = Dup { unDup :: (a, a) }
  deriving newtype (Eq, Ord)
  deriving stock (Show, Functor)

instance Foldable Dup where
  foldMap f (Dup (x, y)) = f x <> f y

instance Eq1 Dup where
  liftEq eq (Dup (x, y)) (Dup (z, w)) = eq x z && eq y w

instance Ord1 Dup where
  liftCompare cmp (Dup (x, y)) (Dup (z, w)) = cmp x z <> cmp y w
