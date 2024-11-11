{-# OPTIONS_GHC -Wno-orphans #-}

module Main (main) where

import Data.Ord
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Numeric.Natural
import Prettyprinter

import Test.QuickCheck

import Test.Compare

import Data.Name
import Language.Problem
import Language.Generics
import Test

type Nat = Natural

instance Arbitrary Nat where
  arbitrary = fromInteger . abs <$> arbitrary

checkSynth :: (Compare a, Interpret a) => Named Problem -> a -> IO ()
checkSynth problem model = do
  print $ "Testing" <+> pretty problem.name <> ":"
  case synth problem.value of
    Nothing -> putStrLn "Synthesis failed..."
    Just result -> do
      quickCheck $ comparison model (interpret result)
  putStrLn ""

main :: IO ()
main = do
  checkSynth "append" $ (++) @Int
  checkSynth "compress" $ compress @Int
  checkSynth "reverse" $ reverse @Int
  checkSynth "cons" $ (:) @Int
  checkSynth "concat" $ concat @[] @Int
  checkSynth "null" $ null @[] @Int
  checkSynth "snoc" $ snoc @Int

  checkSynth "head" $ headMaybe @Int
  checkSynth "last" $ lastMaybe @Int
  checkSynth "tail" $ tailSafe @Int
  checkSynth "init" $ initSafe @Int

  checkSynth "unzip" $ unzip @Int @Int

  checkSynth "member" $ List.elem @[] @Int
  checkSynth "nub" $ List.nub @Int

  checkSynth "ordNub" $ List.nub @Int

  -- It seems that this is non-deterministic!
  checkSynth "clamp" $ curry $ clamp @Int

  checkSynth "replicate" $ repli @Int

  checkSynth "copyFirst" $ copyFirst @Int
  checkSynth "dupli" $ dupli @Int
  checkSynth "allSame" $ allSame @Int

-- Model solutions

compress :: Eq a => [a] -> [a]
compress = map NonEmpty.head . NonEmpty.group

copyFirst :: [a] -> [a]
copyFirst [] = []
copyFirst (x:xs) = x : (x <$ xs)

headMaybe :: [a] -> Maybe a
headMaybe [] = Nothing
headMaybe (x:_) = Just x

lastMaybe :: [a] -> Maybe a
lastMaybe [] = Nothing
lastMaybe xs = Just $ last xs

tailSafe :: [a] -> [a]
tailSafe [] = []
tailSafe (_:xs) = xs

initSafe :: [a] -> [a]
initSafe [] = []
initSafe xs = init xs

repli :: a -> Nat -> [a]
repli x n = replicate (fromIntegral n) x

dupli :: [a] -> [a]
dupli = concatMap \x -> [x,x]

snoc :: a -> [a] -> [a]
snoc x xs = xs ++ [x]

allSame :: Eq a => [a] -> Bool
allSame [] = True
allSame (x:xs) = all (==x) xs
