{-# LANGUAGE DataKinds #-}

module Constraint
  ( All, Each
  , type (**)
  , Trivial
  ) where

import Data.Kind

class    Trivial t
instance Trivial t

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
