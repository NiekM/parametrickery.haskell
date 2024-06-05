{-# LANGUAGE UndecidableInstances #-}

{- |
Module      : Data.Fin
Copyright   : (c) Anonymous 2024
Maintainer  : Anonymous

A wrapper over natural numbers that has an implicit upper bound.

-}
module Data.Fin where

import Data.SBV

import Base
import Data.SBV.Encode
import Data.SBV.Depend

-- | A natural number whose symbolic representation has an upper bound.
newtype Fin = Fin Natural
  deriving newtype (Eq, Ord, Enum, Show, Num, Encode)

instance Dep Fin where
  type Arg Fin = Natural
  depend n x = x .>= 0 .&& x .< n
