{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}

module Data.Functor.Context
  ( Context(..)
  , KeyValue(..)
  , Assoc
  , AllVal, AllKey
  , Name(..)
  ) where

import GHC.TypeLits
import Data.Kind
import Data.Functor.Classes

data KeyValue k v = k :-> v

data Name (k :: Symbol) = Name

instance KnownSymbol k => Show (Name k) where
  show = symbolVal

type Assoc k v = [KeyValue k v]

data Context (fs :: Assoc Symbol (Type -> Type)) a where
  Nil  :: Context '[] a
  Cons :: KnownSymbol k =>
    Name k -> f a -> Context fs a -> Context ((k :-> f) ': fs) a

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
  Cons _ x xs == Cons _ y ys = x == y && xs == ys

instance (Ord a, AllVal Eq1 fs, AllVal Ord1 fs) => Ord (Context fs a) where
  compare Nil Nil = EQ
  compare (Cons _ x xs) (Cons _ y ys) = compare x y <> compare xs ys

instance AllVal Eq1 fs => Eq1 (Context fs) where
  liftEq _ Nil Nil = True
  liftEq eq (Cons _ x xs) (Cons _ y ys) = liftEq eq x y && liftEq eq xs ys

instance (AllVal Eq1 fs, AllVal Ord1 fs) => Ord1 (Context fs) where
  liftCompare _ Nil Nil = EQ
  liftCompare cmp (Cons _ x xs) (Cons _ y ys) =
    liftCompare cmp x y <> liftCompare cmp xs ys
