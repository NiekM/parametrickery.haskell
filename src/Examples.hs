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
    make :: SymVal a => String -> [a] -> Symbolic ()
    make s xs = makeFoldr @Identity @[] @(Const ())
      (Const ()) (Identity <$> xs) [] (tail xs) f ("tail_" <> s)

  -- make @Integer "45678" [4,5,6,7,8]
  make @Integer "4567" [4,5,6,7]
  -- make @Integer "123" [1,2,3]
  make @Bool "TF" [True, False]
  -- makeTail @Bool "T" [True]

-- tail as foldr can be refuted with two input lists of different lengths with
-- unique elements.
tailProofE :: Symbolic ()
tailProofE = do
  f <- symbolicMorphism "u_f" "g_f"
  e <- symbolicMorphism "u_e" "g_e"

  let
    make :: SymVal a => String -> [a] -> Symbolic ()
    make s xs = makeFoldrE (Const ()) (Const ()) (Identity <$> xs) e (tail xs) f ("tail_" <> s)

  -- make @Integer "45678" [4,5,6,7,8]
  make @Integer "4567" [4,5,6,7]
  -- make @Integer "123" [1,2,3]
  make @Bool "TF" [True, False]
  -- make @Bool "T" [True]

-- init as foldr can only be refuted with a singleton list as input.
initProof :: Symbolic ()
initProof = do
  f <- symbolicMorphism "u" "g"

  let
    make :: SymVal a => String -> [a] -> Symbolic ()
    make s xs = makeFoldr @Identity @[] @(Const ())
      (Const ()) (Identity <$> xs) [] (init xs) f ("init_" <> s)

  -- make @Integer "45678" [4,5,6,7,8]
  make @Integer "4567" [4,5,6,7]
  make @Integer "123" [1,2,3]
  make @Bool "TF" [True, False]
  make @Bool "T" [True]

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
    make :: SymVal a => String -> [a] -> Symbolic ()
    make s xs = makeFoldr @Identity @[] @(Const ())
      (Const ()) (Identity <$> xs) [] (switch xs) f ("switch_" <> s)

  make @Integer "4567" [4,5,6,7]
  make @Integer "123" [1,2,3]
  make @Bool "TF" [True, False]
  make @Bool "T" [True]

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
    make :: SymVal a => String -> [a] -> [a] -> Symbolic ()
    make s xs ys = makeFoldr @Identity @[] @(Const ())
      (Const ()) (Identity <$> ys) xs (xs ++ ys) f ("append_" <> s)

  make @Integer "1_2" [1] [2]
  make @Integer "e_12" [] [1,2]
  make @Integer "e_1" [] [1]

  -- make @Integer "123_4" [1,2,3] [4]
  -- make @Integer "12_34" [1,2] [3,4]
  -- make @Integer "12_3" [1,2] [3]

  -- make @Integer "123_4567" [1,2,3] [4,5,6,7]
  -- make @Integer "123_456" [1,2,3] [4,5,6]
  -- make @Integer "123_45" [1,2,3] [4,5]
  -- make @Integer "12_3456" [1,2] [3,4,5,6]
  -- make @Integer "12_345" [1,2] [3,4,5]

-- rotate as foldr is possible.
rotateProof :: Symbolic ()
rotateProof = do
  f <- symbolicMorphism "u" "g"

  let
    make :: SymVal a => String -> [a] -> Symbolic ()
    make s xs = makeFoldr @Identity @[] @(Const ())
      (Const ()) (Identity <$> xs) [] (rotate xs) f ("rotate_" <> s)

  make @Integer "123" [1,2,3]
  make @Bool "TF" [True, False]
  make @Bool "T" [True]

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
    make :: SymVal a => String -> Int -> [a] -> Symbolic ()
    make s n xs = makeFoldr @Identity @[] @(Const Natural)
      (fromIntegral n) (Identity <$> xs) [] (drop n xs) f ("drop_" <> s)

  make @Integer "2_4567" 2 [4,5,6,7]
  -- make @Integer "1_123" 1 [1,2,3]
  make @Integer "2_123" 2 [1,2,3]
  -- make @Bool "1_TF" 1 [True, False]
  -- make @Bool "1_T" 1 [True]

remove :: Int -> [a] -> [a]
remove _ [] = []
remove 0 (_:xs) = xs
remove n (x:xs) = x : remove (n - 1) xs

-- remove as foldr can be refuted, as it generalizes tail.
removeProof :: Symbolic ()
removeProof = do
  f <- symbolicMorphism "u" "g"

  let
    make :: SymVal a => String -> Int -> [a] -> Symbolic ()
    make s n xs = makeFoldr @Identity @[] @(Const Natural)
      (fromIntegral n) (Identity <$> xs) [] (remove n xs) f ("remove_" <> s)

  make @Integer "2_4567" 2 [4,5,6,7]
  -- make @Integer "1_123" 1 [1,2,3]
  make @Integer "2_123" 2 [1,2,3]
  -- make @Bool "1_TF" 1 [True, False]
  -- make @Bool "1_T" 1 [True]

-- take as foldr is possible: foldr (\x r -> take n (x:r)) [].
takeProof :: Symbolic ()
takeProof = do
  f <- symbolicMorphism "u" "g"

  let
    make :: SymVal a => String -> Int -> [a] -> Symbolic ()
    make s n xs = makeFoldr @Identity @[] @(Const Natural)
      (fromIntegral n) (Identity <$> xs) [] (take n xs) f ("take_" <> s)

  make @Integer "2_4567" 2 [4,5,6,7]
  -- make @Integer "1_123" 1 [1,2,3]
  make @Integer "2_123" 2 [1,2,3]
  make @Bool "1_TF" 1 [True, False]
  make @Bool "1_T" 1 [True]

-- intersperse as foldr is possible.
intersperseProof :: Symbolic ()
intersperseProof = do
  f <- symbolicMorphism "u" "g"

  let
    make :: SymVal a => String -> a -> [a] -> Symbolic ()
    make s x xs = makeFoldr @Identity @[] @Identity
      (Identity x) (Identity <$> xs) [] (intersperse x xs) f ("intersperse_" <> s)
  -- make @Integer "3_4567" 3 [4,5,6,7]
  -- make @Integer "4_123" 4 [1,2,3]
  -- make @Bool "T_TF" True [False, False]
  -- make @Bool "F_T" False [True]

  -- Trace complete:
  make @Integer "0_1234" 0 [1,2,3,4]
  make @Integer "0_234" 0 [2,3,4]
  make @Integer "0_34" 0 [3,4]
  make @Integer "0_4" 0 [4]

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
    make :: SymVal a => String -> [a] -> Symbolic ()
    make s xs = makeMap @Identity @Identity @[]
      xs (Identity <$> xs) (Identity <$> reverse xs) f ("rev_" <> s)

  -- make @Integer "palyndrome" [1,2,3,2,1]
  make @Integer "45678" [4,5,6,7,8]
  -- make @Integer "4567" [4,5,6,7]
  -- make @Integer "123" [1,2,3]
  -- make @Bool "TF" [True, False]
  -- make @Bool "T" [True]

revFold :: Symbolic ()
revFold = do
  f <- symbolicMorphism "u" "g"

  let
    make :: SymVal a => String -> [a] -> Symbolic ()
    make s xs = makeFoldr @Identity @[] @(Const ())
      (Const ()) (Identity <$> xs) [] (reverse xs) f ("rev_" <> s)

  make @Integer "4567" [4,5,6,7]
  make @Bool "TF" [True, False]

-- Behaves as expected, u always returns 2! And all intermediate lists have length 2
dupliProof :: Symbolic ()
dupliProof = do

  f <- symbolicMorphism "u" "g"

  let
    make :: SymVal a => String -> [a] -> Symbolic ()
    make s xs = makeConcatMap @Identity (Identity <$> xs) (concatMap (\x -> [x,x]) xs) f ("dupli_" <> s)

  make @Integer "123" [1,2,3]

-- This works as expected when calling
-- >> optimize Lexicographic revMinFold
-- Only shapes are minimized
revMinFold :: Symbolic ()
revMinFold = do
  f <- symbolicMorphism "u" "g"

  let
    make :: SymVal a => String -> [a] -> Symbolic ()
    make s xs = makeMinFoldr @Identity @[] @(Const ())
      (Const ()) (Identity <$> xs) [] (reverse xs) f ("rev_" <> s)

  make @Integer "4567" [4,5,6,7]
  make @Bool "TF" [True, False]

-- TODO: can we use getModelDictionary and getModelUIFuns to extract the values
-- from the minimized result to synthesize a solution?

-- TODO: using the Query monad, we can incrementally add constraints, for
-- example to perform synthesis search.



-- From Data.SBV:

-- modelUIFuns :: [(String, (SBVType, Either String ([([CV], CV)], CV)))]
--   ^ Mapping of uninterpreted functions to association lists in the model.
--     Note that an uninterpreted constant (function of arity 0) will be stored
--     in the 'modelAssocs' field. Left is used when the function returned is too
--     difficult for SBV to figure out what it means

-- Apparently the results are too difficult to convert back to real values...