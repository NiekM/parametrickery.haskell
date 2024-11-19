{-# LANGUAGE RequiredTypeArguments #-}

module Main (main) where

import Base

import Data.Typeable

import Test.QuickCheck hiding (Success, Failure)

import Test.Compare

import Data.Tree.Binary
import Language.Generics

roundTrip :: forall a ->
  (Arbitrary a, FromExpr a, ToExpr a, Eq a, Show a, Typeable a) => IO ()
roundTrip t = do
  putStrLn $ "Roundtripping " <> show (typeRep $ Proxy @t)
  quickCheck . comparison Just $ fromExpr . toExpr @t

main :: IO ()
main = do
  roundTrip Int
  roundTrip Bool
  roundTrip Ordering
  roundTrip (Maybe Int)
  roundTrip (type [Int])
  roundTrip (Either Int Int)
  roundTrip (Tree Int Int)
