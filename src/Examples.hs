{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeAbstractions #-}

module Examples (module Examples) where

import Data.SBV (ConstraintSet, SymVal)
import Numeric.Natural
import Data.List (intersperse)

import Data.Functor.Identity
import Data.Functor.Const
import Data.Functor.Product
import Data.Functor.Compose

import Control.Monad
import Data.Monoid (Last(..), getLast)

import Dependent
import Symbolic
import Container
import Sugar

-- NOTE: for some reason, using Char for the monomorphic inputs causes z3 to diverge!??

-- TODO: can we somehow combine Bench and Bench2?

data Input f where
  Any :: SymVal a => f a -> Input f

data Bench f = forall g. Container g => Bench
  { name      :: String
  , reference :: forall a. f a -> g a
  , inputs    :: [Input f]
  }

int :: f Integer -> Input f
int = Any

foldrBasic :: Bench [] -> ConstraintSet
foldrBasic (Bench name reference inputs) = do
  f <- symbolicMorphism "u" "g"

  forM_ (zip inputs [0 :: Int ..]) \(Any xs, i) ->
    makeFoldr (Const ()) (Identity <$> xs) (reference []) (reference xs) f (name <> "_" <> show i)

-- tail is not a fold
-- can be refuted with two input lists of different lengths with unique elements.
tailBench :: Bench []
tailBench = Bench "tail" safeTail
  [ Any "4567"
  , Any [True, False]
  ]

-- last is a fold
lastBench :: Bench []
lastBench = Bench "last" safeLast
  [ Any "4567"
  , Any [True, False]
  ]

-- init is not a fold
-- refuted with a singleton list as input.
-- TODO: what about the base case?
initBench :: Bench []
initBench = Bench "init" safeInit
  [ Any "4567"
  , Any "123"
  , Any [True, False]
  , Any [True]
  ]

-- rotate is a fold (invertible)
switchBench :: Bench []
switchBench = Bench "switch" switch
  [ Any @Integer [4,5,6,7]
  , Any @Integer [1,2,3]
  , Any [True, False]
  , Any [True]
  ]

-- alternate is a fold (invertible)
alternateBench :: Bench []
alternateBench = Bench "alternate" alternate
  [ Any "4567"
  , Any "123"
  , Any [True, False]
  , Any [True]
  ]

-- rotate is a fold (invertible)
reverseBench :: Bench []
reverseBench = Bench "reverse" reverse
  [ Any "4567"
  , Any "hello"
  ]

-- rotate is a fold (invertible/special case of shift)
rotateBench :: Bench []
rotateBench = Bench "rotate" rotate
  [ Any "4567"
  , Any "123"
  , Any [True, False]
  , Any [True]
  ]

-- shift is a fold (invertible)
-- _shiftBench :: Bench (Product (Const Int) [])
-- _shiftBench = Bench "shift" _
--   []
-- _shiftBench = Bench2 "shift" shiftl
  -- [ Any2 1 [4 :: Integer,5,6,7]
  -- , Any2 1 [1 :: Integer,2,3]
  -- , Any2 1 [True, False]
  -- , Any2 1 [True]
  -- , Any2 2 [4 :: Integer,5,6,7]
  -- , Any2 2 [1 :: Integer,2,3]
  -- , Any2 2 [True, False]
  -- , Any2 2 [True]
  -- ]

-- data Input_ c f where
--   Input_ :: SymVal a => c -> f a -> Input_ c f

-- data Bench_ c f = forall g. Container g => Bench_
--   { _name  :: String
--   , _model :: forall a. c -> f a -> g a
--   , _input :: [Input_ c f]
--   }

-- -- TODO: change to Bench_ _ (Compose [] f) or something
-- checkFold :: Ref c => Bench_ c [] -> ConstraintSet
-- checkFold (Bench_ name model input) = do
--   f <- symbolicMorphism "u" "g"

--   forM_ (zip input [0 :: Int ..]) \(Input_ x xs, i) ->
--     makeFoldr (Const x) (Identity <$> xs) (model x []) (model x xs) f (name <> "_" <> show i)

-- type Input0 = Input_ ()
-- type Bench0 = Bench_ ()

-- pattern Input0 :: () => SymVal a => f a -> Input0 f
-- pattern Input0 x = Input_ () x

-- foo :: (forall a. () -> f a -> g a) -> forall a. f a -> g a
-- foo f = f ()

-- pattern Bench0 :: () => Container g => String -> (forall a. f a -> g a) -> [Input0 f] -> Bench0 f
-- pattern Bench0 n m i <- Bench_ n (foo -> m) i
--   where Bench0 n m i = Bench_ n (const m) i

-- -- last is a fold
-- lastBench_ :: Bench0 []
-- lastBench_ = Bench0 "last" safeLast
--   [ Input0 "4567"
--   , Input0 [True, False]
--   ]

-- TODO: have FoldBench contain inputs and outputs, and add function fromModel.
-- Even better, create a typeclass with fromModel as a class method.
-- data FoldInput f where
--   FoldInput :: SymVal a => [f a] -> FoldInput f
-- data FoldBench = forall f g. (Container f, Container g) => FoldBench
--   { name'   :: String
--   , model'  :: forall a. [f a] -> g a
--   , inputs' :: [FoldInput f]
--   }

-- -- Corresponding to the pipeline in Fig. 5 of the paper:
-- -- ∃𝑝. ( ∀𝑎. 𝑝 : [𝐹 𝑎] → 𝐺 𝑎 ) ∧ ( ∃𝑓. 𝑝 = foldr 𝑓 𝑦0 ) ∧ ( 𝑝 [𝑥_𝑛−1 · · ·𝑥_0] ≡ 𝑦_𝑛 )
-- checkFoldBench :: FoldBench -> ConstraintSet
-- checkFoldBench (FoldBench name model inputs) = do
--   f <- symbolicMorphism "u" "g"

--   forM_ (zip inputs [0 :: Int ..]) \(FoldInput xs, i) ->
--     makeFoldr (Const ()) xs (model []) (model xs) f (name <> "_" <> show i)

-- type FoldInput' = FoldInput Identity

-- foldInput' :: forall a. SymVal a => [a] -> FoldInput'
-- foldInput' = FoldInput @a . coerce

-- foldBench' :: Container g => String -> (forall a. [a] -> g a) -> [FoldInput'] -> FoldBench
-- foldBench' name model inputs = FoldBench name (model . coerce) inputs

-- -- last is a fold
-- lastBench' :: FoldBench
-- lastBench' = foldBench' "last" safeLast
--   [ foldInput' "4567"
--   , foldInput' [True, False]
--   ]


-- makeFoldr :: (Container f, Container g, Container h, SymVal a)
--   => h a -> [f a] -> g a -> g a -> SMorphism (Product h (Product f g)) g
--   -> String -> Symbolic ()

data Mono f where
  Mono :: SymVal a => f a -> Mono f

data FoldBench = forall f g. (Container f, Container g) => FoldBench
  { base :: forall a. g a
  -- TODO: add an extra product for additional arguments?
  , examples :: [Mono (Product (Compose [] f) g)]
  }

-- Corresponding to the pipeline in Fig. 5 of the paper:
-- ∃𝑝. ( ∀𝑎. 𝑝 : [𝐹 𝑎] → 𝐺 𝑎 ) ∧ ( ∃𝑓. 𝑝 = foldr 𝑓 𝑦0 ) ∧ ( 𝑝 [𝑥_𝑛−1 · · ·𝑥_0] ≡ 𝑦_𝑛 )
checkFoldBench :: FoldBench -> ConstraintSet
checkFoldBench (FoldBench base io) = do
  f <- symbolicMorphism "u" "g"

  forM_ (zip io [0 :: Int ..]) \(Mono (Pair xs y), i) ->
    makeFoldr (Const ()) (getCompose xs) base y f ("f_" <> show i)

fromModel :: (Container f, Container g) => (forall a. [f a] -> g a) -> [Mono (Compose [] f)] -> FoldBench
fromModel f = FoldBench (f []) . map \(Mono @a xs) -> Mono @a (Pair xs (f (getCompose xs)))

fromModel' :: (Container g) => (forall a. [a] -> g a) -> [Mono []] -> FoldBench
fromModel' f = fromModel @Identity (f . map sugar) . map \(Mono @a xs) -> Mono @a (desugar xs)

-- tail is not a fold
-- can be refuted with two input lists of different lengths with unique elements.
tailBench' :: FoldBench
tailBench' = fromModel' safeTail
  [ Mono @Integer [4,5,6,7]
  , Mono [True, False]
  ]

-- last is a fold
lastBench' :: FoldBench
lastBench' = fromModel' safeLast
  [ Mono @Integer [4,5,6,7]
  , Mono [True, False]
  ]

-- init is not a fold
-- refuted with a singleton list as input.
initBench' :: FoldBench
initBench' = fromModel' safeInit
  [ Mono @Integer [4,5,6,7]
  , Mono @Integer [1,2,3]
  , Mono [True, False]
  , Mono [True]
  ]

-- rotate is a fold (invertible)
switchBench' :: FoldBench
switchBench' = fromModel' switch
  [ Mono @Integer [4,5,6,7]
  , Mono @Integer [1,2,3]
  , Mono [True, False]
  , Mono [True]
  ]

-- alternate is a fold (invertible)
alternateBench' :: FoldBench
alternateBench' = fromModel' alternate
  [ Mono @Integer [4,5,6,7]
  , Mono @Integer [1,2,3]
  , Mono [True, False]
  , Mono [True]
  ]

-- rotate is a fold (invertible)
reverseBench' :: FoldBench
reverseBench' = fromModel' reverse
  [ Mono @Integer [4,5,6,7]
  , Mono @Integer [1,2,3]
  ]

-- rotate is a fold (invertible/special case of shift)
rotateBench' :: FoldBench
rotateBench' = fromModel' rotate
  [ Mono @Integer [4,5,6,7]
  , Mono @Integer [1,2,3]
  , Mono [True, False]
  , Mono [True]
  ]


data Input2 i f where
  Any2 :: SymVal a => i -> f a -> Input2 i f

data Bench2 i f = forall g. Container g => Bench2
  { name2   :: String
  , ref2    :: forall a. i -> f a -> g a
  , inputs2 :: [Input2 i f]
  }

foldrBasic2 :: Ref i => Bench2 i [] -> ConstraintSet
foldrBasic2 (Bench2 name reference inputs) = do
  f <- symbolicMorphism "u" "g"

  forM_ (zip inputs [0 :: Int ..]) \(Any2 x xs, i) ->
    makeFoldr (Const x) (Identity <$> xs) (reference x []) (reference x xs) f (name <> "_" <> show i)

-- shift is a fold (invertible)
shiftBench :: Bench2 Int []
shiftBench = Bench2 "shift" shiftl
  [ Any2 1 [4 :: Integer,5,6,7]
  , Any2 1 [1 :: Integer,2,3]
  , Any2 1 [True, False]
  , Any2 1 [True]
  , Any2 2 [4 :: Integer,5,6,7]
  , Any2 2 [1 :: Integer,2,3]
  , Any2 2 [True, False]
  , Any2 2 [True]
  ]

-- drop is not a fold (generalizes tail)
dropBench :: Bench2 Int []
dropBench = Bench2 "drop" drop
  [ Any2 1 [4 :: Integer,5,6,7]
  , Any2 1 [1 :: Integer,2,3]
  , Any2 1 [True, False]
  , Any2 1 [True]
  , Any2 2 [4 :: Integer,5,6,7]
  , Any2 2 [1 :: Integer,2,3]
  , Any2 2 [True, False]
  , Any2 2 [True]
  ]

-- remove is not a fold (generalizes tail)
removeBench :: Bench2 Natural []
removeBench = Bench2 "remove" remove
  [ Any2 1 [4 :: Integer,5,6,7]
  , Any2 0 [1 :: Integer,2,3]
  , Any2 1 [True, False]
  , Any2 1 [True]
  , Any2 2 [4 :: Integer,5,6,7]
  , Any2 2 [1 :: Integer,2,3]
  , Any2 0 [True, False]
  , Any2 2 [True]
  ]

-- index is not a fold
-- It seems that a fold of type `[a] -> Maybe a` can only be `head`, `last`, or
-- `const Nothing`.
indexBench :: Bench2 Natural []
indexBench = Bench2 "index" index
  [ Any2 1 [4 :: Integer,5,6,7]
  , Any2 0 [1 :: Integer,2,3]
  , Any2 1 [True, False]
  , Any2 1 [True]
  , Any2 2 [4 :: Integer,5,6,7]
  , Any2 2 [1 :: Integer,2,3]
  , Any2 0 [True, False]
  , Any2 2 [True]
  ]

-- take is a fold (foldr (\x r -> take n (x:r)) [])
takeBench :: Bench2 Int []
takeBench = Bench2 "take" take
  [ Any2 1 [4 :: Integer,5,6,7]
  , Any2 0 [1 :: Integer,2,3]
  , Any2 1 [True, False]
  , Any2 1 [True]
  , Any2 2 [4 :: Integer,5,6,7]
  , Any2 2 [1 :: Integer,2,3]
  , Any2 0 [True, False]
  , Any2 2 [True]
  ]






-- TODO: 
-- > do we have more benchmarks? do they fit this schema?
-- > actually have a reference of type [f a] -> [g a]?
-- data MapBench = MapBench String (forall a. [a] -> [a]) [Input []]

-- mapBasic :: MapBench -> ConstraintSet
-- mapBasic (MapBench name reference inputs) = do
--   f <- symbolicMorphism "u" "g"

--   forM_ (zip inputs [0 :: Int ..]) \(Any xs, i) ->
--     makeMap xs (Identity <$> xs) (Identity <$> reference xs) f (name <> "_" <> show i)













------ Reference Implementations ------

safeTail :: [a] -> [a]
safeTail = drop 1

safeInit :: [a] -> [a]
safeInit [] = []
safeInit xs = init xs

safeLast :: [a] -> Maybe a
safeLast = getLast . foldMap (Last . Just)

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

alternate :: [a] -> [a]
alternate (x:y:ys) = y:x:alternate ys
alternate xs = xs

shiftl :: Int -> [a] -> [a]
shiftl _ [] = []
shiftl n xs = zs ++ ys
  where
    m = n `mod` length xs
    (ys, zs) = splitAt m xs

rotate :: [a] -> [a]
rotate [] = []
rotate (x:xs) = foldr (:) [x] xs

remove :: Natural -> [a] -> [a]
remove _ [] = []
remove 0 (_:xs) = xs
remove n (x:xs) = x : remove (n - 1) xs

index :: Natural -> [a] -> Maybe a
index _ [] = Nothing
index 0 (x:_) = Just x
index n (_:xs) = index (n - 1) xs




------ Functions as Folds ------

rotate_ :: [a] -> [a]
rotate_ = foldr f [] where
  f x xs = case unsnoc xs of
    Nothing -> [x]
    Just (ys, y) -> y:ys ++ [x]

alternate_ :: [a] -> [a]
alternate_ = foldr f [] where
  f x r = alternate (x:alternate r)

shiftl_ :: Int -> [a] -> [a]
shiftl_ n = foldr f [] where
  f x r = shiftl n (x:shiftl (-n) r)

switch_ :: [a] -> [a]
switch_ = foldr f [] where
  f x r = switch (x:switch r)

intersperse_ :: a -> [a] -> [a]
intersperse_ x = foldr f [] where
  f y r = intersperse x (y:outersperse r)

outersperse :: [a] -> [a]
outersperse [] = []
outersperse [x] = [x]
outersperse (x:_:xs) = x:outersperse xs

-- NOTE: it may seem that all idempotent functions are folds by this
-- construction, but that is not the case. For example copy_first is idemptotent
-- but *not* defined using `f x r = copy_first (x:r)`.
take_ :: Int -> [a] -> [a]
take_ n = foldr f [] where
  f x r = take n (x:r)



------ OTHER ------

-- tail as foldr can be refuted with two input lists of different lengths with
-- unique elements.
-- tailProofE :: ConstraintSet
-- tailProofE = do
--   f <- symbolicMorphism "u_f" "g_f"
--   e <- symbolicMorphism "u_e" "g_e"

--   let
--     make :: SymVal a => String -> [a] -> ConstraintSet
--     make s xs = makeFoldrE (Const ()) (Const ()) (Identity <$> xs) e (safeTail xs) f ("tail_" <> s)

--     makes :: [Input []] -> ConstraintSet
--     makes = zipWithM_ (\i (Any x) -> make (show i) x) [0 :: Int ..]

--   makes
--     [ int [4,5,6,7]
--     , Any [True, False]
--     ]

-- append cannot be defined as a fold over the right argument!
appendWrong :: ConstraintSet
appendWrong = do
  f <- symbolicMorphism "u" "g"

  let
    make :: SymVal a => String -> [a] -> [a] -> ConstraintSet
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

-- intersperse as foldr is possible.
intersperseProof :: ConstraintSet
intersperseProof = do
  f <- symbolicMorphism "u" "g"

  let
    make :: SymVal a => String -> a -> [a] -> ConstraintSet
    make s x xs = makeFoldr @Identity @[] @Identity
      (Identity x) (Identity <$> xs) [] (intersperse x xs) f ("intersperse_" <> s)
  -- make @Integer "3_4567" 3 [4,5,6,7]
  -- make @Integer "4_123" 4 [1,2,3]
  -- make @Bool "T_TF" True [False, False]
  -- make @Bool "F_T" False [True]

  mapM_ (\(i, (x, xs)) -> make @Integer (show i) x xs) $ zip [0 :: Int ..]
    [ (0, [1,2,3,4])
    , (0, [2,3,4])
    , (0, [3,4])
    , (0, [4])
    ]

  -- Trace complete:
  -- make @Integer "0_1234" 0 [1,2,3,4]
  -- make @Integer "0_234" 0 [2,3,4]
  -- make @Integer "0_34" 0 [3,4]
  -- make @Integer "0_4" 0 [4]

-- Conclusion
intersperse__ :: a -> [a] -> [a]
intersperse__ x = foldr f []
  where
    f y [] = [y]
    f y (z:zs) = y:x:z:zs

-- Behaves as expected, u always returns 2! And all intermediate lists have length 2
dupliProof :: ConstraintSet
dupliProof = do

  f <- symbolicMorphism "u" "g"

  let
    make :: SymVal a => String -> [a] -> ConstraintSet
    make s xs = makeConcatMap @Identity (Identity <$> xs) (concatMap (\x -> [x,x]) xs) f ("dupli_" <> s)

  make @Integer "123" [1,2,3]

-- This works as expected when calling
-- >> optimize Lexicographic revMinFold
-- Only shapes are minimized
revMinFold :: ConstraintSet
revMinFold = do
  f <- symbolicMorphism "u" "g"

  let
    make :: SymVal a => String -> [a] -> ConstraintSet
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
