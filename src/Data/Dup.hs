module Data.Dup where

import Base

newtype Dup a = Dup { unDup :: (a, a) }
  deriving newtype (Eq, Ord)
  deriving stock (Show, Functor, Foldable, Traversable)

instance Eq1 Dup where
  liftEq eq (Dup (x, y)) (Dup (z, w)) = eq x z && eq y w

instance Ord1 Dup where
  liftCompare cmp (Dup (x, y)) (Dup (z, w)) = cmp x z <> cmp y w

instance Show1 Dup where
  liftShowsPrec :: forall a.
    (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> Dup a -> ShowS
  liftShowsPrec sp sl p (Dup (x, y)) s
    | p > 10    = '(' : res ++ ')' : s
    | otherwise = res ++ s
    where
      res = "Dup {unDup = " ++ liftShowsPrec2 sp sl sp sl 0 (x, y) "}"
