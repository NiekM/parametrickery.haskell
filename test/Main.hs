{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main (main) where

import Test.QuickCheck
import Numeric.Natural
import Test.Hspec hiding (Arg)
import Test.Hspec.QuickCheck

import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Functor.Identity
import Data.Functor.Const
import Data.Functor.Product
import Data.Functor.Sum

import Data.SBV
import Data.SBV.Depend
import Data.Container

instance Arbitrary Natural where
  arbitrary = natural

natural :: Gen Natural
natural = fromInteger . getNonNegative <$> arbitrary

instance (Arbitrary1 f, Arbitrary1 g) => Arbitrary1 (Sum f g) where
  liftArbitrary arb = oneof
    [ InL <$> liftArbitrary arb
    , InR <$> liftArbitrary arb
    ]
  liftShrink shr (InL x) = [ InL x' | x' <- liftShrink shr x]
  liftShrink shr (InR y) = [ InR y' | y' <- liftShrink shr y]

instance (Arbitrary1 f, Arbitrary1 g, Arbitrary a) =>
  Arbitrary (Sum f g a) where
  arbitrary = liftArbitrary arbitrary
  shrink = liftShrink shrink

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

  describe "refine holds on encoded values" do
    prop "@()"               $ refineHolds @()
    prop "@Bool"             $ refineHolds @Bool
    prop "@Int"              $ refineHolds @Int
    prop "@Char"             $ refineHolds @Char
    prop "@Natural"          $ refineHolds @Natural
    prop "@(Int, Int)"       $ refineHolds @(Int, Int)
    prop "@(Either Int Int)" $ refineHolds @(Either Int Int)

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

-- | Check if encoding a refinement types results in a value for which
-- 'Data.SBV.Refine.refine' holds.
refineHolds :: forall a. Ref a => a -> Bool
refineHolds x = case unliteral (refine @a $ literal $ encode x) of
  Nothing -> error "Something went wrong: somehow not a literal"
  Just b -> b

-- | Check if encoding a dependent type and its argument results in values for
-- which 'Data.SBV.Depend.depend' holds.
dependHolds :: forall a. Dep a => Arg a -> a -> Bool
dependHolds x y = case unliteral (depend @a x' y') of
  Nothing -> error "Something went wrong: somehow not a literal"
  Just b -> b
  where
    x' = literal (encode x)
    y' = literal (encode y)

-- | Check whether turning a 'Data.Functor.Functor' into its
-- 'Data.Container.Core.Container' representation and back results in the same
-- value.
containerRoundTrip :: (Container f, Eq (f a)) => f a -> Bool
containerRoundTrip x = x == fromContainer (toContainer x)

-- | Check whether the shapes and positions of a 'Data.Container.Core.Container'
-- are properly constrained.
containerDependencies :: (Container f, Eq (f a)) => f a -> Bool
containerDependencies x = refineHolds s && all (dependHolds s) (Map.keys p)
  where Extension s p = toContainer x

--- Injectivity ---

genVec :: (Arbitrary a, Ord a) => Int -> IO [a]
genVec n = Set.toAscList . Set.fromList <$> generate (vectorOf n arbitrary)

injective :: (Arbitrary a, Ord a, Ord b, Show a, Show b) => (a -> b) -> Spec
injective f = beforeAll (genVec 300) do
  it "is injective" $ \xs -> checkInjective f xs mempty

-- | Check for the injectivity of a function based on a list of inputs, using an
-- accumulating Map.
--
-- As opposed to the more natural but inefficient:
--
-- @
-- checkInjective :: (Eq a, Eq b) => (a -> b) -> a -> a -> Property
-- checkInjective f x y = f x == f y ==> x == y
-- @
--
checkInjective :: (Eq a, Ord b, Show a, Show b) =>
  (a -> b) -> [a] -> Map b a -> Expectation
checkInjective _ [] _ = return ()
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
