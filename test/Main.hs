{-# LANGUAGE RequiredTypeArguments #-}

module Main (main) where

import Base

import Data.Typeable

import Test.QuickCheck (Arbitrary)
import Test.Tasty
import Test.Tasty.QuickCheck (testProperty)

import Data.Tree.Binary
import Language.Arbitrary ()
import Language.Generics

showType :: forall a -> Typeable a => String
showType t = show . typeRep $ Proxy @t

roundTrip :: forall a ->
  (Arbitrary a, FromExpr a, ToExpr a False, Eq a, Show a, Typeable a)
  => TestTree
roundTrip t = testProperty ("@(" <> showType t <> ")")
  \(e :: t) -> fromExpr (toExpr e) == Just e

roundTrips :: TestTree
roundTrips = testGroup "fromExpr . toExpr == Just"
  [ roundTrip Int
  , roundTrip (type Bool)
  , roundTrip (type Ordering)
  , roundTrip (Maybe Int)
  , roundTrip (type [Int])
  , roundTrip (Either Int Int)
  , roundTrip (Tree Int Int)
  ]

main :: IO ()
main = defaultMain $ testGroup "all"
  [ roundTrips
  ]

  -- TODO:
  -- [ ] checkRelation (computeRelation ...) == True
  -- [ ] applyRule ... (checkExample ...) == ...
  -- [ ] reconstruct . reconstruct == reconstruct
  -- [ ] normalize . normalize == normalize
  -- [x] (normalize :: Value -> Value) == id

  -- [ ] `greedy` always succeeds
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
