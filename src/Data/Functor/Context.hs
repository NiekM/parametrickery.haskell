{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeAbstractions #-}

module Data.Functor.Context
  ( Context(Nil, Cons)
  , KeyValue(..)
  , Assoc
  , Name(..)
  ) where

import GHC.TypeLits
import Data.Kind
import Data.Functor.Classes
import Data.List (intercalate)
import Pretty

data KeyValue k v = k :-> v

data Name (k :: Symbol) = Name

instance KnownSymbol k => Show (Name k) where
  show = symbolVal

type Assoc k v = [KeyValue k v]

data Context (fs :: Assoc Symbol (Type -> Type)) a where
  Nil :: Context '[] a
  Ext :: KnownSymbol k =>
    Name k -> f a -> Context fs a -> Context ((k :-> f) ': fs) a

{-# COMPLETE Nil, Cons #-}
pattern Cons :: () => (fs ~ ((k :-> f) : fs'), KnownSymbol k) =>
  f a -> Context fs' a -> Context fs a
pattern Cons x xs = Ext Name x xs

type family AllKey (c :: k -> Constraint) (ts :: Assoc k v) :: Constraint where
  AllKey c '[] = ()
  AllKey c ((k :-> v) ': ts) = (c k, AllKey c ts)

type family AllVal (c :: v -> Constraint) (ts :: Assoc k v) :: Constraint where
  AllVal c '[] = ()
  AllVal c ((k :-> v) ': ts) = (c v, AllVal c ts)

deriving instance AllVal Functor  fs => Functor  (Context fs)
deriving instance AllVal Foldable fs => Foldable (Context fs)
deriving instance (AllVal Functor fs, AllVal Foldable fs, AllVal Traversable fs)
  => Traversable (Context fs)

instance (Eq a, AllVal Eq1 fs) => Eq (Context fs a) where
  Nil == Nil = True
  Cons x xs == Cons y ys = x == y && xs == ys

instance (Ord a, AllVal Eq1 fs, AllVal Ord1 fs) => Ord (Context fs a) where
  compare Nil Nil = EQ
  compare (Cons x xs) (Cons y ys) = compare x y <> compare xs ys

instance AllVal Eq1 fs => Eq1 (Context fs) where
  liftEq _ Nil Nil = True
  liftEq eq (Cons x xs) (Cons y ys) = liftEq eq x y && liftEq eq xs ys

instance (AllVal Eq1 fs, AllVal Ord1 fs) => Ord1 (Context fs) where
  liftCompare _ Nil Nil = EQ
  liftCompare cmp (Cons x xs) (Cons y ys) =
    liftCompare cmp x y <> liftCompare cmp xs ys

instance AllVal Show1 fs => Show1 (Context fs) where
  liftShowsPrec :: forall a.
    (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> Context fs a -> ShowS
  liftShowsPrec _ _ _ Nil s = "{ }" <> s
  liftShowsPrec shPrec shList _ ctx s =
    '{' : intercalate ", " (strs ctx) ++ '}' : s
    where
      strs :: forall gs. AllVal Show1 gs => Context gs a -> [String]
      strs = \case
        Nil -> []
        Ext v x xs ->
          (show v <> " = " <> liftShowsPrec shPrec shList 0 x "") : strs xs

instance (AllVal Show1 fs, Show a) => Show (Context fs a) where
  show x = liftShowsPrec showsPrec showList 0 x ""

instance AllVal Pretty ctx => Pretty (Context ctx) where
  pretty _ Nil s = s
  pretty _ ctx s = '{' : intercalate ", " (strs ctx) ++ '}' : s
    where
      strs :: (AllVal Pretty c, Show a) =>
        Context c a -> [String]
      strs = \case
        Nil -> []
        Ext v x xs -> show v <> " = " <> pretty 0 x "" : strs xs
