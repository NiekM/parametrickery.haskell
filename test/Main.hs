{-# LANGUAGE RequiredTypeArguments #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Main (main) where

import Numeric.Natural
import System.Timeout
import Data.Typeable

import Prettyprinter
import Test.QuickCheck

import Model qualified as Model
import Test.Compare

import Data.Name
import Data.Tree.Binary
import Language.Problem
import Language.Generics
import Test

type Nat = Natural

instance Arbitrary Nat where
  arbitrary = fromInteger . abs <$> arbitrary

instance Arbitrary2 Tree where
  liftArbitrary2 gen1 gen2 = sized \n -> do
    k <- choose (0, n)
    go k
    where
      go 0 = Leaf <$> gen2
      go n = do
        k <- choose (0, n - 1)
        Node <$> go k <*> gen1 <*> go (n - k - 1)

instance (Arbitrary a, Arbitrary b) => Arbitrary (Tree a b) where
  arbitrary = arbitrary2

data Bench = forall a. (Compare a, Interpret a) => Bench
  { problem :: Named Problem
  , model :: a
  }

testBench :: Bench -> IO ()
testBench (Bench problem model) = do
  print $ "Testing" <+> pretty problem.name <> ":"
  x <- timeout 1_000_000 case synth problem.value of
    Nothing -> return Nothing
    Just r -> return $ Just r
  case x of
    Nothing -> putStrLn "Synthesis failed: timeout"
    Just Nothing -> putStrLn "Synthesis failed: exhaustive"
    Just (Just r) -> quickCheck . withMaxSize 25 $
      comparison model (interpret r)

benches :: [Bench]
benches =
  [ Bench "allSame"           $ Model.allSame @Int
  , Bench "append"            $ Model.append @Int
  , Bench "breadthFirst"      $ Model.breadthFirst @Int @Int
  , Bench "cartesian"         $ Model.cartesian @Int
  , Bench "clamp"             $ Model.clamp @Int
  , Bench "compress"          $ Model.compress @Int
  , Bench "concat"            $ Model.concat @Int
  , Bench "cons"              $ Model.cons @Int
  , Bench "copyFirst"         $ Model.copyFirst @Int
  , Bench "copyLast"          $ Model.copyLast @Int
  -- TODO: it is all about phrasing! If we say that our tool cannot synthesize
  -- deleteMax, that's not very impressive, but if we show that our tool
  -- exhaustively searched the program space, that sounds much more impressive.
  -- Same for `ordNub`, `splitAt`, etc.
  , Bench "deleteMax"         $ Model.deleteMax @Int
  , Bench "depth"             $ Model.depth @Int @Int
  , Bench "drop"              $ Model.drop @Int
  , Bench "dupli"             $ Model.dupli @Int
  , Bench "head"              $ Model.head @Int
  , Bench "index"             $ Model.index @Int
  , Bench "init"              $ Model.init @Int
  , Bench "inorder"           $ Model.inorder @Int @Int
  , Bench "insert"            $ Model.insert @Int
  , Bench "last"              $ Model.last @Int
  , Bench "length"            $ Model.length @Int
  , Bench "levels"            $ Model.levels @Int @Int
  , Bench "maximum"           $ Model.maximum @Int
  , Bench "member"            $ Model.member @Int
  , Bench "mostCommon"        $ Model.mostCommon @Int
  , Bench "nub"               $ Model.nub @Int
  , Bench "null"              $ Model.null @Int
  , Bench "ordNub"            $ Model.ordNub @Int
  , Bench "partitionEithers"  $ Model.partitionEithers @Int @Int
  , Bench "pivot"             $ Model.pivot @Int
  , Bench "preorder"          $ Model.preorder @Int @Int
  , Bench "replicate"         $ Model.replicate @Int
  , Bench "reverse"           $ Model.reverse @Int
  , Bench "shiftl"            $ Model.shiftl @Int
  , Bench "shiftr"            $ Model.shiftr @Int
  , Bench "size"              $ Model.size @Int @Int
  , Bench "snoc"              $ Model.snoc @Int
  , Bench "sort"              $ Model.sort @Int
  , Bench "sorted"            $ Model.sorted @Int
  , Bench "splitAt"           $ Model.splitAt @Int
  , Bench "swap"              $ Model.swap @Int @Int
  , Bench "tail"              $ Model.tail @Int
  , Bench "take"              $ Model.take @Int
  , Bench "unzip"             $ Model.unzip @Int @Int
  , Bench "zip"               $ Model.zip @Int @Int
  ]

roundTrip :: forall a ->
  (Arbitrary a, FromExpr a, ToExpr a, Eq a, Show a, Typeable a) => IO ()
roundTrip t = do
  putStrLn $ "Roundtripping " <> show (typeRep $ Proxy @t)
  quickCheck . comparison Just $ fromExpr . toExpr @t

main :: IO ()
main = do
  mapM_ testBench benches

  roundTrip Int
  roundTrip Bool
  roundTrip Ordering
  roundTrip (Maybe Int)
  roundTrip (type [Int])
  roundTrip (Either Int Int)
  roundTrip (Tree Int Int)
