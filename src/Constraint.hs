{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}

module Constraint
  ( Dict(..)
  , All, Each
  , type (**), type (|-)
  , HasType
  , Trivial
  ) where

import Data.Kind

data Dict :: Constraint -> Type where
  Dict :: c => Dict c

class    Trivial t
instance Trivial t

class    (forall a. p a => q a) => p |- q
instance (forall a. p a => q a) => p |- q

class    (t ~ u) => HasType t u
instance (t ~ u) => HasType t u

class And (c :: k -> Constraint) (d :: k -> Constraint) (t :: k)
instance (c t, d t) => And c d t

type family All (c :: k -> Constraint) (ts :: [k]) :: Constraint where
  All c '[] = ()
  All c (t ': ts) = (c t, All c ts)

type family Each (cs :: [k -> Constraint]) (t :: k) :: Constraint where
  Each '[]       t = ()
  Each (c ': cs) t = (c t, Each cs t)

type family (**) (cs :: [k -> Constraint]) (ts :: [k]) :: Constraint where
  '[] ** _ = ()
  (c ': cs) ** ts = (All c ts, cs ** ts)
