{-# LANGUAGE RequiredTypeArguments #-}

module Main (main) where

import Base

import Data.Typeable
import Data.Functor.Identity

import Test.QuickCheck (Arbitrary)
import Test.Tasty
import Test.Tasty.QuickCheck (testProperty, forAll, discard, classify)
import Control.Carrier.Reader
import Control.Carrier.Throw.Either

import Data.Tree.Binary
import Language.Arbitrary qualified as Arbitrary
import Language.Container.Relation
import Language.Container.Morphism
import Language.Expr
import Language.Type
import Language.Problem
import Language.Prelude
import Language.Generics
import Synth

showType :: forall a -> Typeable a => String
showType t = show . typeRep $ Proxy @t

roundTrip :: forall a ->
  (Arbitrary a, FromExpr a, ToExpr a False, Eq a, Show a, Typeable a)
  => TestTree
roundTrip t = testProperty ("@(" <> showType t <> ")")
  \(e :: t) -> fromExpr (toExpr e) == Just e

roundTrips :: TestTree
roundTrips = testGroup "fromExpr . toExpr == Just"
  [ roundTrip (type Int)
  , roundTrip (type Bool)
  , roundTrip (type Ordering)
  , roundTrip (type (Maybe Int))
  , roundTrip (type [Int])
  , roundTrip (type (Either Int Int))
  , roundTrip (type (Tree Int Int))
  ]

normValue :: TestTree
normValue = testProperty "normalize == id @Value"
  \(v :: Value) -> normalize v == v

relationConsistency :: TestTree
relationConsistency = testProperty "checkRelation m (computeRelation m c)" $
  forAll (Arbitrary.valueMap free) \m ->
  forAll (Arbitrary.constraint free) \c ->
    checkRelation m (computeRelation m c)
  where free = ["a", "b", "c"]

runCheck :: ReaderC Context (ThrowC Conflict Identity) a -> Either Conflict a
runCheck = run . runThrow @Conflict . runReader datatypes

ruleConsistency :: TestTree
ruleConsistency = testProperty
  "applyRule (checkExample s (Example i o)) i == Just o" $
  forAll (Arbitrary.sig free) \signature ->
  forAll (Arbitrary.example signature) \example ->
    case runCheck $ checkExample signature example of
      Left _err -> discard
      Right rule ->
        classify (null $ holes rule.output) "simple" $
        applyRule rule example.inputs == Just example.output
  where free = ["a", "b"]

main :: IO ()
main = defaultMain $ testGroup "all"
  [ roundTrips
  , normValue
  , relationConsistency
  , ruleConsistency
  ]

-- NOTE: greedy does not always succeed. we cannot pattern match if a case is
-- missing. if we do allow this, we do not know what to do for a hole without
-- examples. greedy does always succeed when the example is total, but how do we
-- generate total examples?

-- greedySucceeds :: TestTree
-- greedySucceeds = testProperty "greedy succeeds" $
--   forAll (Arbitrary.problem ["a", "b"]) \problem ->
--     case runCheck $ check problem of
--       Left _err -> discard
--       Right _ -> case synthesize def { tactic = greedy } problem of
--         Failure _ -> False
--         Success _ -> True

  -- TODO:
  -- [x] checkRelation (computeRelation ...) == True
  -- [x] applyRule ... (checkExample ...) == ...
  -- [ ] reconstruct . reconstruct == reconstruct
  -- [ ] normalize . normalize == normalize
  -- [x] (normalize :: Value -> Value) == id
  -- [?] `greedy` always succeeds
  -- [ ] tactics "preserve" totality (the total amount of missing cases should stay the same)
  -- [ ] isMap ==> isFold
  -- [ ] isMap ==> isMapSome
  -- [ ] isFilter ==> isFold
  -- [ ] isFilter ==> isFilterSome
  -- [ ] reversible ==> isFold
  -- [ ] preserveRealizable introCtr
  -- [ ] preserveRealizable introTuple
  -- [ ] preserveRealizable (anywhere elim)
  -- [ ] preserveRealizable (anywhere2 elimEq)
  -- [ ] preserveRealizable (anywhere2 elimOrd)
