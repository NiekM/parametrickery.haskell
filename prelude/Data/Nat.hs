{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Nat where

import Prelude
import Numeric.Natural
import Test.QuickCheck

type Nat = Natural

instance Arbitrary Nat where
  arbitrary = fromInteger . abs <$> arbitrary
