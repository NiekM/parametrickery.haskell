module Examples (module Examples) where

import Data.SBV (Symbolic, SymVal)
import Numeric.Natural
import Data.List (intersperse)

import Data.Functor.Identity
import Data.Functor.Const

import Symbolic

-- tail as foldr can be refuted with two input lists of different lengths with
-- unique elements.
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

-- tail as foldr can be refuted with two input lists of different lengths with
-- unique elements.
tailProofE :: Symbolic ()
tailProofE = do
  f <- symbolicMorphism "u_f" "g_f"
  e <- symbolicMorphism "u_e" "g_e"

  let
    makeTail :: SymVal a => String -> [a] -> Symbolic ()
    makeTail s xs = makeFoldrE (Const ()) (Const ()) (Identity <$> xs) e (tail xs) f ("tail_" <> s)

  -- makeTail @Integer "45678" [4,5,6,7,8]
  makeTail @Integer "4567" [4,5,6,7]
  -- makeTail @Integer "123" [1,2,3]
  makeTail @Bool "TF" [True, False]
  -- makeTail @Bool "T" [True]

-- init as foldr can only be refuted with a singleton list as input.
initProof :: Symbolic ()
initProof = do
  f <- symbolicMorphism "u" "g"

  let
    makeInit :: SymVal a => String -> [a] -> Symbolic ()
    makeInit s xs = makeFoldr @Identity @[] @(Const ())
      (Const ()) (Identity <$> xs) [] (init xs) f ("init_" <> s)

  -- makeInit @Integer "45678" [4,5,6,7,8]
  makeInit @Integer "4567" [4,5,6,7]
  makeInit @Integer "123" [1,2,3]
  makeInit @Bool "TF" [True, False]
  makeInit @Bool "T" [True]

unsnoc :: [a] -> Maybe ([a], a)
unsnoc = foldr f Nothing where
  f a Nothing = Just ([], a)
  f a (Just (xs, x)) = Just (a:xs, x)

-- Swap the first and last element of a list.
switch :: [a] -> [a]
switch [] = []
switch (x:xs) = case unsnoc xs of
  Nothing -> [x]
  Just (ys, y) -> y : ys ++ [x]

-- switch is possible, since it can distinguish the length of the output list.
switchProof :: Symbolic ()
switchProof = do
  f <- symbolicMorphism "u" "g"

  let
    makeSwitch :: SymVal a => String -> [a] -> Symbolic ()
    makeSwitch s xs = makeFoldr @Identity @[] @(Const ())
      (Const ()) (Identity <$> xs) [] (switch xs) f ("switch_" <> s)

  makeSwitch @Integer "4567" [4,5,6,7]
  makeSwitch @Integer "123" [1,2,3]
  makeSwitch @Bool "TF" [True, False]
  makeSwitch @Bool "T" [True]

shiftl :: Int -> [a] -> [a]
shiftl n xs = zs ++ ys
  where
    m = n `mod` length xs
    (ys, zs) = splitAt m xs

-- shift is possible, since it can match the output list against the input int.
shiftlProof :: Symbolic ()
shiftlProof = do
  f <- symbolicMorphism "u" "g"

  let
    make :: SymVal a => String -> Int -> [a] -> Symbolic ()
    make s n xs = makeFoldr @Identity @[] @(Const Int)
      (Const n) (Identity <$> xs) [] (shiftl n xs) f ("shift_" <> show n <> "_" <> s)

  make @Integer "4567" 1 [4,5,6,7]
  make @Integer "123" 1 [1,2,3]
  make @Bool "TF" 1 [True, False]
  make @Bool "T" 1 [True]

  make @Integer "4567" 2 [4,5,6,7]
  make @Integer "123" 2 [1,2,3]
  make @Bool "FT" 2 [False, True]
  make @Bool "T" 2 [True]

alternate :: [a] -> [a]
alternate (x:y:ys) = y:x:alternate ys
alternate xs = xs

-- Apparently alternate is also possible...
altProof :: Symbolic ()
altProof = do
  f <- symbolicMorphism "u" "g"

  let
    make :: SymVal a => String -> [a] -> Symbolic ()
    make s xs = makeFoldr @Identity @[] @(Const ())
      (Const ()) (Identity <$> xs) [] (alternate xs) f ("alternate_" <> s)

  make @Integer "4567" [4,5,6,7]
  make @Integer "123" [1,2,3]
  make @Bool "TF" [True, False]
  make @Bool "T" [True]

rotate :: [a] -> [a]
rotate [] = []
rotate (x:xs) = foldr (:) [x] xs

-- append cannot be defined as a fold over the right argument!
appendWrong :: Symbolic ()
appendWrong = do
  f <- symbolicMorphism "u" "g"

  let
    makeAppend :: SymVal a => String -> [a] -> [a] -> Symbolic ()
    makeAppend s xs ys = makeFoldr @Identity @[] @(Const ())
      (Const ()) (Identity <$> ys) xs (xs ++ ys) f ("append_" <> s)

  makeAppend @Integer "1_2" [1] [2]
  makeAppend @Integer "e_12" [] [1,2]
  makeAppend @Integer "e_1" [] [1]

  -- makeAppend @Integer "123_4" [1,2,3] [4]
  -- makeAppend @Integer "12_34" [1,2] [3,4]
  -- makeAppend @Integer "12_3" [1,2] [3]

  -- makeAppend @Integer "123_4567" [1,2,3] [4,5,6,7]
  -- makeAppend @Integer "123_456" [1,2,3] [4,5,6]
  -- makeAppend @Integer "123_45" [1,2,3] [4,5]
  -- makeAppend @Integer "12_3456" [1,2] [3,4,5,6]
  -- makeAppend @Integer "12_345" [1,2] [3,4,5]

-- rotate as foldr is possible.
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

-- Conclusion
rotate_ :: [a] -> [a]
rotate_ = foldr f [] where
  f x xs = case unsnoc xs of
    Nothing -> [x]
    Just (ys, y) -> y:ys ++ [x]

-- drop as foldr can be refuted, as it generalizes tail.
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

remove :: Int -> [a] -> [a]
remove _ [] = []
remove 0 (_:xs) = xs
remove n (x:xs) = x : remove (n - 1) xs

-- remove as foldr can be refuted, as it generalizes tail.
removeProof :: Symbolic ()
removeProof = do
  f <- symbolicMorphism "u" "g"

  let
    makeRemove :: SymVal a => String -> Int -> [a] -> Symbolic ()
    makeRemove s n xs = makeFoldr @Identity @[] @(Const Natural)
      (fromIntegral n) (Identity <$> xs) [] (remove n xs) f ("remove_" <> s)

  makeRemove @Integer "2_4567" 2 [4,5,6,7]
  -- makeRemove @Integer "1_123" 1 [1,2,3]
  makeRemove @Integer "2_123" 2 [1,2,3]
  -- makeRemove @Bool "1_TF" 1 [True, False]
  -- makeRemove @Bool "1_T" 1 [True]

-- take as foldr is possible: foldr (\x r -> take n (x:r)) [].
takeProof :: Symbolic ()
takeProof = do
  f <- symbolicMorphism "u" "g"

  let
    makeTake :: SymVal a => String -> Int -> [a] -> Symbolic ()
    makeTake s n xs = makeFoldr @Identity @[] @(Const Natural)
      (fromIntegral n) (Identity <$> xs) [] (take n xs) f ("take_" <> s)

  makeTake @Integer "2_4567" 2 [4,5,6,7]
  -- makeTake @Integer "1_123" 1 [1,2,3]
  makeTake @Integer "2_123" 2 [1,2,3]
  makeTake @Bool "1_TF" 1 [True, False]
  makeTake @Bool "1_T" 1 [True]

-- intersperse as foldr is possible.
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

-- Behaves as expected, u always returns 2! And all intermediate lists have length 2
dupliProof :: Symbolic ()
dupliProof = do

  f <- symbolicMorphism "u" "g"

  let
    makeDupli :: SymVal a => String -> [a] -> Symbolic ()
    makeDupli s xs = makeConcatMap @Identity (Identity <$> xs) (concatMap (\x -> [x,x]) xs) f ("dupli_" <> s)

  makeDupli @Integer "123" [1,2,3]

-- This works as expected when calling
-- >>> optimize Lexicographic revMinFold
-- Only shapes are minimized
revMinFold :: Symbolic ()
revMinFold = do
  f <- symbolicMorphism "u" "g"

  let
    makeRev :: SymVal a => String -> [a] -> Symbolic ()
    makeRev s xs = makeMinFoldr @Identity @[] @(Const ())
      (Const ()) (Identity <$> xs) [] (reverse xs) f ("rev_" <> s)

  makeRev @Integer "4567" [4,5,6,7]
  makeRev @Bool "TF" [True, False]

-- TODO: can we use getModelDictionary and getModelUIFuns to extract the values
-- from the minimized result to synthesize a solution?

-- TODO: using the Query monad, we can incrementally add constraints, for
-- example to perform synthesis search.