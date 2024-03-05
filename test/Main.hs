{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main (main) where

import Test.QuickCheck
import Numeric.Natural
import Test.Hspec
import Test.Hspec.QuickCheck

import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Functor.Identity
import Data.Functor.Const
import Data.Functor.Product
import Data.Functor.Sum

import Data.SBV.Depend
import Data.Container

instance Arbitrary Natural where
  arbitrary = natural

natural :: Gen Natural
natural = fromInteger . getNonNegative <$> arbitrary

instance (Arbitrary1 f, Arbitrary1 g) => Arbitrary1 (Sum f g) where
  liftArbitrary arb = oneof [InL <$> liftArbitrary arb, InR <$> liftArbitrary arb]
  liftShrink shr (InL x) = [ InL x' | x' <- liftShrink shr x]
  liftShrink shr (InR y) = [ InR y' | y' <- liftShrink shr y]

instance (Arbitrary1 f, Arbitrary1 g, Arbitrary a) => Arbitrary (Sum f g a) where
  arbitrary = liftArbitrary arbitrary
  shrink = liftShrink shrink

-- TODO: how to easily test for many different types?
-- TODO: use approach inspired by quickcheck-classes library
-- so: use functions that generate tests for a type. i.e. rawLaws, refLaws, depLaws.

-- TODO: is there any way to make this less verbose?
-- i.e. can we pass a list 'types' and check at each of them?

main :: IO ()
main = hspec do
  describe "encode" do
    describe "@()"               . injective $ encode @()
    describe "@Bool"             . injective $ encode @Bool
    describe "@Int"              . injective $ encode @Int
    describe "@Char"             . injective $ encode @Char
    describe "@Natural"          . injective $ encode @Natural
    describe "@(Int, Int)"       . injective $ encode @(Int, Int)
    describe "@(Either Int Int)" . injective $ encode @(Either Int Int)

  describe "ref holds on encoded values" do
    prop "@()"               $ refHolds @()
    prop "@Bool"             $ refHolds @Bool
    prop "@Int"              $ refHolds @Int
    prop "@Char"             $ refHolds @Char
    prop "@Natural"          $ refHolds @Natural
    prop "@(Int, Int)"       $ refHolds @(Int, Int)
    prop "@(Either Int Int)" $ refHolds @(Either Int Int)

  describe "container laws" do
    describe "roundtrip" do
      prop "@[]"       $ containerRoundTrip @[] @Int
      prop "@Maybe"    $ containerRoundTrip @Maybe @Int
      prop "@Identity" $ containerRoundTrip @Identity @Int
      prop "@Const"    $ containerRoundTrip @(Const Int) @Int
      prop "@Product"  $ containerRoundTrip @(Product [] Maybe) @Int
      prop "@Sum"      $ containerRoundTrip @(Sum [] Maybe) @Int

    describe "dependencies" do
      prop "@[]"       $ containerDependencies @[] @Int
      prop "@Maybe"    $ containerDependencies @Maybe @Int
      prop "@Identity" $ containerDependencies @Identity @Int
      prop "@Const"    $ containerDependencies @(Const Int) @Int
      prop "@Product"  $ containerDependencies @(Product [] Maybe) @Int
      prop "@Sum"      $ containerDependencies @(Sum [] Maybe) @Int

--- Injectivity ---

-- TODO: is there some way to shrink the results?

genVec :: (Arbitrary a, Ord a) => Int -> IO [a]
genVec n = Set.toAscList . Set.fromList <$> generate (vectorOf n arbitrary)

asExpected :: Expectation
asExpected = return ()

injective :: (Arbitrary a, Ord a, Ord b, Show a, Show b) => (a -> b) -> Spec
injective f = beforeAll (genVec 300) do
  it "is injective" $ \xs -> checkInjective f xs mempty

checkInjective :: (Eq a, Ord b, Show a, Show b) =>
  (a -> b) -> [a] -> Map b a -> Expectation
checkInjective _ [] _ = asExpected
checkInjective f (x:xs) m =
  case Map.insertLookupWithKey (const const) (f x) x m of
    (Just y, _) | x /= y -> expectationFailure $ unwords
      [ "the inputs"
      , show x, "and", show y
      , "should return unique values but they both return"
      , show (f x)
      , show xs
      ]
    (_, m') -> checkInjective f xs m'

-- As opposed to the more natural but inefficient:
--
-- injective :: (Eq a, Eq b) => (a -> b) -> a -> a -> Property
-- injective f x y = f x == f y ==> x == y
--
-- Usage:
-- > hspec do
-- >  describe "(+1)" $ injective @Int (+1)
-- >  describe "(`div` 2)" $ injective @Int (`div` 2)
--
-- (+1)
--   is injective [v]
-- (`div` 2)
--   is injective [x]
--
