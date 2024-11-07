{-# OPTIONS_GHC -Wno-orphans #-}

module Main (main) where

import Data.Ord
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Numeric.Natural

import Test.QuickCheck

import Test.Compare
import Test

type Nat = Natural

instance Arbitrary Nat where
  arbitrary = fromInteger . abs <$> arbitrary

main :: IO ()
main = do
  quickCheck $ comparison ((++) @Int) (tryOut "append")
  quickCheck $ comparison (compress @Int) (tryOut "compress")
  quickCheck $ comparison (reverse @Int) (tryOut "reverse")
  quickCheck $ comparison ((:) @Int) (tryOut "cons")
  quickCheck $ comparison (concat @[] @Int) (tryOut "concat")
  quickCheck $ comparison (null @[] @Int) (tryOut "null")
  quickCheck $ comparison (snoc @Int) (tryOut "snoc")

  quickCheck $ comparison (headMaybe @Int) (tryOut "head")
  quickCheck $ comparison (lastMaybe @Int) (tryOut "last")
  quickCheck $ comparison (tailSafe @Int) (tryOut "tail")
  quickCheck $ comparison (initSafe @Int) (tryOut "init")

  quickCheck $ comparison (unzip @Int @Int) (tryOut "unzip")

  quickCheck $ comparison (List.elem @[] @Int) (tryOut "member")
  quickCheck $ comparison (List.nub @Int) (tryOut "nub")

  quickCheck $ comparison (List.nub @Int) (tryOut "ordNub")
  quickCheck $ comparison (curry $ clamp @Int) (tryOut "clamp")

  quickCheck $ comparison (repli @Int) (tryOut "replicate")

  quickCheck $ comparison (copyFirst @Int) (tryOut "copyFirst")
  quickCheck $ comparison (dupli @Int) (tryOut "dupli")
  quickCheck $ comparison (allSame @Int) (tryOut "allSame")

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
