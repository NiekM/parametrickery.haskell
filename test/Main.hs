{-# LANGUAGE BlockArguments #-}
module Main (main) where

import Dependent
import Test.QuickCheck
import Numeric.Natural
import Test.Hspec
import Test.Hspec.QuickCheck

import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

instance Arbitrary Natural where
  arbitrary = natural

natural :: Gen Natural
natural = fromInteger . getNonNegative <$> arbitrary

-- TODO: how to easily test for many different types?
-- TODO: use approach inspired by quickcheck-classes library
-- so: use functions that generate tests for a type. i.e. rawLaws, refLaws, depLaws.

-- TODO: is there any way to make this less verbose?
-- i.e. can we pass a list 'types' and check at each of them?

main :: IO ()
main = hspec do
  describe "raw" do
    describe "@()"               . injective $ raw @()
    describe "@Bool"             . injective $ raw @Bool
    describe "@Int"              . injective $ raw @Int
    describe "@Char"             . injective $ raw @Char
    describe "@Natural"          . injective $ raw @Natural
    describe "@(Int, Int)"       . injective $ raw @(Int, Int)
    describe "@(Either Int Int)" . injective $ raw @(Either Int Int)
  -- TODO: also check HasRaw instances of dependent arguments.

  describe "ref holds on raw values" do
    prop "@()"               $ refLaws @()
    prop "@Bool"             $ refLaws @Bool
    prop "@Int"              $ refLaws @Int
    prop "@Char"             $ refLaws @Char
    prop "@Natural"          $ refLaws @Natural
    prop "@(Int, Int)"       $ refLaws @(Int, Int)
    prop "@(Either Int Int)" $ refLaws @(Either Int Int)

  describe "(`div` 2)" $ injective @Int \x -> abs (20 - x)

--- Injectivity ---

-- TODO: is there some way to shrink the results?

genVec :: (Arbitrary a, Ord a) => Int -> IO [a]
genVec n = Set.toAscList . Set.fromList <$> generate (vectorOf n arbitrary)

asExpected :: Expectation
asExpected = return ()

injective :: (Arbitrary a, Ord a, Ord b, Show a, Show b) => (a -> b) -> Spec
injective f = beforeAll (genVec 300) do
  it "is injective" $ \xs -> checkInjective f xs mempty

checkInjective :: (Eq a, Ord b, Show a, Show b) => (a -> b) -> [a] -> Map b a -> Expectation
checkInjective _ [] _ = asExpected
checkInjective f (x:xs) m = case Map.insertLookupWithKey (const const) (f x) x m of
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
