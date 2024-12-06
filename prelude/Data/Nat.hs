{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Nat where

import Prelude
import Data.Bifunctor
import Numeric.Natural
import System.Random
import Test.QuickCheck

type Nat = Natural

fairNat :: Integer -> Nat
fairNat n
  | n >= 0 = fromInteger (2 * n)
  | otherwise = fromInteger (- (2 * n) - 1)

instance Arbitrary Nat where
  arbitrary = fairNat <$> arbitrary

instance Random Nat where
  random g = fairNat `first` random g
