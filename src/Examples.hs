module Examples (module Examples) where

import Data.SBV (Symbolic, SymVal)
import Numeric.Natural
import Data.List (intersperse)

import Data.Functor.Identity
import Data.Functor.Const

import Symbolic

tailProof :: Symbolic ()
tailProof = do
  f <- symbolicMorphism "u" "g"

  let
    makeTail :: SymVal a => String -> [a] -> Symbolic ()
    makeTail s xs = makeFoldr @Identity @[] @(Const ())
      (Const ()) (Identity <$> xs) [] (tail xs) f ("tail_" <> s)

  -- makeTail @Integer "45678" [4,5,6,7,8]
  makeTail @Integer "4567" [4,5,6,7]
  -- makeTail @Integer "123" [1,2,3]
  makeTail @Bool "TF" [True, False]
  -- makeTail @Bool "T" [True]

rotate :: [a] -> [a]
rotate [] = []
rotate (x:xs) = foldr (\y r -> y:r) [x] xs

-- Maybe rotate can be a fold? Or it is too hard to prove
rotateProof :: Symbolic ()
rotateProof = do
  f <- symbolicMorphism "u" "g"

  let
    makeRotate :: SymVal a => String -> [a] -> Symbolic ()
    makeRotate s xs = makeFoldr @Identity @[] @(Const ())
      (Const ()) (Identity <$> xs) [] (rotate xs) f ("rotate_" <> s)

  makeRotate @Integer "123" [1,2,3]
  makeRotate @Bool "TF" [True, False]
  makeRotate @Bool "T" [True]

-- -- Conclusion
rotate_ :: [a] -> [a]
rotate_ = foldr f []
  where
    f x xs = case unsnoc xs of
      Nothing -> [x]
      Just (ys, y) -> y:ys ++ [x]

    unsnoc :: [a] -> Maybe ([a], a)
    unsnoc = foldr g Nothing 

    g a Nothing = Just ([], a)
    g a (Just (xs, x)) = Just (a:xs, x)

dropProof :: Symbolic ()
dropProof = do
  f <- symbolicMorphism "u" "g"

  let
    makeDrop :: SymVal a => String -> Int -> [a] -> Symbolic ()
    makeDrop s n xs = makeFoldr @Identity @[] @(Const Natural)
      (fromIntegral n) (Identity <$> xs) [] (drop n xs) f ("drop_" <> s)

  makeDrop @Integer "2_4567" 2 [4,5,6,7]
  -- makeDrop @Integer "1_123" 1 [1,2,3]
  makeDrop @Integer "2_123" 2 [1,2,3]
  -- makeDrop @Bool "1_TF" 1 [True, False]
  -- makeDrop @Bool "1_T" 1 [True]

intersperseProof :: Symbolic ()
intersperseProof = do
  f <- symbolicMorphism "u" "g"

  let
    makeIntersperse :: SymVal a => String -> a -> [a] -> Symbolic ()
    makeIntersperse s x xs = makeFoldr @Identity @[] @Identity
      (Identity x) (Identity <$> xs) [] (intersperse x xs) f ("intersperse_" <> s)
  -- makeIntersperse @Integer "3_4567" 3 [4,5,6,7]
  -- makeIntersperse @Integer "4_123" 4 [1,2,3]
  -- makeIntersperse @Bool "T_TF" True [False, False]
  -- makeIntersperse @Bool "F_T" False [True]

  -- Trace complete:
  makeIntersperse @Integer "0_1234" 0 [1,2,3,4]
  makeIntersperse @Integer "0_234" 0 [2,3,4]
  makeIntersperse @Integer "0_34" 0 [3,4]
  makeIntersperse @Integer "0_4" 0 [4]

-- Conclusion
intersperse_ :: a -> [a] -> [a]
intersperse_ x = foldr f []
  where
    f y [] = [y]
    f y (z:zs) = y:x:z:zs

revProof :: Symbolic ()
revProof = do
  f <- symbolicMorphism "u" "g"

  let
    makeRev :: SymVal a => String -> [a] -> Symbolic ()
    makeRev s xs = makeMap @Identity @Identity @[]
      xs (Identity <$> xs) (Identity <$> reverse xs) f ("rev_" <> s)

  -- makeRev @Integer "palyndrome" [1,2,3,2,1]
  makeRev @Integer "45678" [4,5,6,7,8]
  -- makeRev @Integer "4567" [4,5,6,7]
  -- makeRev @Integer "123" [1,2,3]
  -- makeRev @Bool "TF" [True, False]
  -- makeRev @Bool "T" [True]

revFold :: Symbolic ()
revFold = do
  f <- symbolicMorphism "u" "g"

  let
    makeRev :: SymVal a => String -> [a] -> Symbolic ()
    makeRev s xs = makeFoldr @Identity @[] @(Const ())
      (Const ()) (Identity <$> xs) [] (reverse xs) f ("rev_" <> s)

  makeRev @Integer "4567" [4,5,6,7]
  makeRev @Bool "TF" [True, False]