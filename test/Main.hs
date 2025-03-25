{-# LANGUAGE RequiredTypeArguments #-}

module Main (main) where

import Base

import Data.Text qualified as Text
import Data.Typeable
import Data.Functor.Identity

import Test.QuickCheck (Arbitrary)
import Test.Tasty
import Test.Tasty.QuickCheck (testProperty, forAll, discard, classify, withMaxSize)
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
import Tactic
import Synth
import Bench

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
main = do
  problems <- forM testBench \model -> do
    problem <- loadProblem model.name
    return $ fmap (problem,) model

  defaultMain $ testGroup "all"
    [ roundTrips
    , normValue
    , relationConsistency
    , ruleConsistency
    , synthesisSucceeds problems
    ]

synthesisSucceeds :: [Named (Problem, Model)] -> TestTree
synthesisSucceeds problems = testGroup "synthesis" $ problems <&> \(Named name (problem, model)) ->
  testProperty (Text.unpack name.getName) . withMaxSize 25 $ testSynthesis args problem model
  where args = def { settings = defaultSettings { removeIrrelevant = False } }

testBench :: [Named Model]
testBench = models & filter \model -> model.name `elem`
  [ "null"
  , "head"
  , "last"
  , "tail"
  , "reverse"
  , "append"
  , "unzip"
  , "concat"
  ]

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
