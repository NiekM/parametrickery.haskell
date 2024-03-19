{-# LANGUAGE DataKinds #-}

module Constraint
  ( All
  , Trivial
  ) where

import Data.Kind

class    Trivial t where
instance Trivial t

type family All (c :: k -> Constraint) (ts :: [k]) :: Constraint where
  All c '[] = ()
  All c (t ': ts) = (c t, All c ts)
