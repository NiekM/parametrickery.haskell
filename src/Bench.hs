{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE DataKinds #-}

module Bench (module Bench) where

import Data.SBV hiding (rotate)
import Data.SBV.Control (SMTOption(..))
import Data.SBV.Refine
import Data.List (intersperse, genericLength, tails)

import Base
import Data.Foldable

import Control.Monad
import Data.Monoid (Last(..), getLast)

import Symbolic
import Data.Container

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map

-- NOTE: for some reason, using Char for the monomorphic inputs causes z3 to diverge!??

data Mono c f where
  Mono :: forall a c f. c a => f a -> Mono c f

mapMono :: (forall a. c a => f a -> g a) -> Mono c f -> Mono c g
mapMono f (Mono @a x) = Mono @a (f x)

type Mono' = Mono SymVal

type FoldInput f g h = Product (Product h (Compose [] f)) g
data FoldBench = forall f g h. (Container f, Container g, Container h) =>
  FoldBench
  { base :: forall a. h a -> g a
  , examples :: [Mono' (FoldInput f g h)]
  }

-- Corresponding to the pipeline in Fig. 5 of the paper:
-- TODO: the paper is missing the additional parameter H a
-- ∃𝑝. ( ∀𝑎. 𝑝 : [𝐹 𝑎] → 𝐺 𝑎 ) ∧ ( ∃𝑓. 𝑝 = foldr 𝑓 𝑦0 ) ∧ ( 𝑝 [𝑥_𝑛−1 ··· 𝑥_0] ≡ 𝑦_𝑛 )
checkFoldBench :: FoldBench -> ConstraintSet
checkFoldBench (FoldBench base io) = do
  f <- symbolicMorphism "u" "g"

  forM_ (zip io [0 :: Int ..]) \(Mono (Pair (Pair c xs) y), i) ->
    makeFoldr c (getCompose xs) (base c) y f ("f_" <> show i)

-- NoCtx version (what exactly is the difference? `foldr f` as opposed to `foldr f e`?)
-- This means that the base case is not available in the function argument
-- We call this "reduced form"
--
-- NOTE: this "reduced" form is a bit silly. It's just a specific case of
-- restricting contexts. We could (should) be explicit about the different
-- contexts of both holes, rather than have a shared context that might be left
-- out in either hole.
--
-- In the case of append/prepend, we could argue that (++) as a fold could work
-- for both arguments, but that the "correct" one should be found first because
-- it is a simpler scheme (with less shared context).
--
checkFoldBenchReduced :: FoldBench -> ConstraintSet
checkFoldBenchReduced (FoldBench base io) = do
  f <- symbolicMorphism "u" "g"

  forM_ (zip io [0 :: Int ..]) \(Mono (Pair (Pair c xs) y), i) ->
    makeFoldr (Const ()) (getCompose xs) (base c) y f ("f_" <> show i)

fromModel :: (Container f, Container g, Container h) =>
  (forall a. h a -> [f a] -> g a) -> [Mono' (Product h (Compose [] f))] -> FoldBench
fromModel f = FoldBench (\c -> f c []) . map
  \(Mono @a i@(Pair c xs)) -> Mono @a (Pair i (f c (getCompose xs)))

-- For functions of the form `foldr f e`
fromModel' :: (Container g) => (forall a. [a] -> g a) -> [Mono' []] -> FoldBench
fromModel' f = FoldBench @Identity (\_ -> f []) . map
  \(Mono @a xs) -> Mono @a (Pair (Pair (Const ()) (coerce xs)) (f xs))

-- For functions of the form `\c -> foldr f e`
fromModel1 :: (Ref c, Container g) => (forall a. c -> [a] -> g a) ->
  [(c, Mono' [])] -> FoldBench
fromModel1 f = FoldBench @Identity (\(Const c) -> f c []) . map
  \(c, Mono @a xs) -> Mono @a (Pair (Pair (Const c) (coerce xs)) (f c xs))

isSat :: ConstraintSet -> IO Bool
isSat = isSatisfiableWith settings

settings :: SMTConfig
settings = defaultSMTCfg
  { solverSetOptions = ReproducibleResourceLimit 10_000_000
  : solverSetOptions defaultSMTCfg
  }
  -- , verbose = True }

checkAll :: [(String, FoldBench)] -> IO ()
checkAll xs = forM_ xs \(name, bench) -> do
  let name' = take width $ name ++ ':' : repeat ' '
  s <- isSat (checkFoldBench bench)
  putStrLn $ name' ++ if s then "Satisfiable" else "Unsatisfiable"
  where width = 2 + maximum (map (length . fst) xs)

checkAll' :: [(String, FoldBench)] -> IO ()
checkAll' xs = forM_ xs \(name, bench) -> do
  let name' = take width $ name ++ ':' : repeat ' '
  s <- isSatisfiableWith (settings { timing = PrintTiming }) (checkFoldBench bench)
  putStrLn $ name' ++ if s then "Satisfiable" else "Unsatisfiable"
  where width = 2 + maximum (map (length . fst) xs)


------ :: [a] -> g a ------

listInputs :: [Mono' []]
listInputs =
  [ Mono @Integer [1,2,3]
  , Mono          [True, False]
  , Mono          [()]
  ]

-- listInputs :: [Mono' []]
-- listInputs =
--   [ Mono @Integer [4,5,6,7]
--   , Mono @Integer [1,2,3]
--   , Mono [True, False]
--   , Mono [True]
--   , Mono @Integer []
--   ]

simpleBenches :: [(String, FoldBench)]
simpleBenches =
  [ ("tail"     , fromModel' safeTail  listInputs)
  -- , ("mayTail"  , fromModel' maybeTail listInputs)
  , ("init"     , fromModel' safeInit  listInputs)
  , ("last"     , fromModel' safeLast  listInputs)
  -- NOTE: last in terms of Either works but takes much longer...
  , ("last'"    , fromModel' safeLast' listInputs)
  , ("switch"   , fromModel' switch    listInputs)
  , ("alternate", fromModel' alternate listInputs)
  , ("reverse"  , fromModel' reverse   listInputs)
  , ("rotate"   , fromModel' rotate    listInputs)
  , ("length"   , fromModel' len       listInputs)
  -- NOTE: these should be easy, but fail...
  , ("unsnoc"   , fromModel' unsnoc'   listInputs)
  -- , ("uncons"   , fromModel' uncons'   listInputs)
  ]

-- mkComposed :: [f a] -> Compose [] f a
-- mkComposed = Pair (()) . Compose

-- otherBenches :: [(String, FoldBench)]
-- otherBenches =
--   [ ("concat"   , fromModel (\(Const ()) -> concat)
--     (nestedInputs <&> mapMono (Pair (Const ()))))
--   -- TODO: composed containers
--   -- , ("transpose", fromModel (\(Const ()) -> Compose . transpose) nestedInputs)
--   ]

-- tail      is not a fold: refuted with two input lists of different lengths with unique elements.
-- init      is not a fold: refuted with a singleton list as input.
-- last      is a fold
-- switch    is a fold (invertible)
-- alternate is a fold (invertible)
-- rotate    is a fold (invertible)
-- rotate    is a fold (invertible/special case of shift)

------ :: Num n => n -> [a] -> g a ------

withNum :: Num a => [(a, Mono' [])]
withNum = map (1,) listInputs ++ map (2,) listInputs

numBenches :: [(String, FoldBench)]
numBenches =
  [ ("shift"  , fromModel1 shiftl withNum)
  , ("drop"   , fromModel1 drop'  withNum)
  , ("remove" , fromModel1 remove withNum)
  -- , ("index"  , fromModel1 index  withNum)
  , ("take"   , fromModel1 take'  withNum)
  ]

-- these are all not folds in "reduced form", i.e. when the number is not in scope of the function

------ :: h a -> [a] -> g a ------

fromModel2 :: (Container h, Container g) => (forall a. h a -> [a] -> g a) -> [Mono' (Product h [])] -> FoldBench
fromModel2 f = FoldBench @Identity (\x -> f x []) . map
  \(Mono @a (Pair x xs)) -> Mono @a (Pair (Pair x (coerce xs)) (f x xs))

list2Inputs :: [Mono' (Product [] [])]
list2Inputs =
  [ Mono @Integer $ Pair [1] [2]
  , Mono @Integer $ Pair [] [1,2]
  , Mono @Integer $ Pair [] [1]
  ]

-- NOTE: both are satisfiable, but append only if the base case is available in the function argument.

-- listBenches :: [(String, FoldBench)]
-- listBenches =
--   [ ("append" , fromModel2 append  list2Inputs)
--   , ("prepend", fromModel2 prepend list2Inputs)
--   ]

-- allBenches :: [(String, FoldBench)]
-- allBenches = simpleBenches ++ numBenches ++ listBenches

-- testBench :: FoldBench
-- testBench = fromModel' testFun [Mono @Integer [1,2]]

-- NOTE: why does this not work??
-- testFun :: [a] -> Sum (Const ()) [] a
-- testFun = InR
-- testFun _ = InL (Const ())
-- testFun = maybe (InL (Const ())) (InR . Identity) . safeLast

-- testFun :: [a] -> [a]
-- testFun = id

-- THIS BREAKS:
-- Why exactly? It might be a bug in Dep (XOR a b)
-- It seems that this error only occurs with a list of at least 2 values: i.e.
-- an uninterpreted intermediate result is unconstrained somehow? Is it possible
-- that it's trying an infinite amount of nonsensical values?
-- TODO: write out a single intermediate result and check what it tries to do

testFun :: [a] -> Sum Identity (Const ()) a
testFun = maybe (InR (Const ())) (InL . Identity) . safeHead


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

drop' :: Natural -> [a] -> [a]
drop' = drop . fromIntegral

take' :: Natural -> [a] -> [a]
take' = take . fromIntegral

safeTail :: [a] -> [a]
safeTail = drop 1

safeTail' :: [a] -> Sum [] (Const ()) a
safeTail' [] = InR (Const ())
safeTail' (_:xs) = InL xs

-- This one also takes too long to solve...
maybeTail :: [a] -> Compose Maybe [] a
maybeTail [] = Compose Nothing
maybeTail (_:xs) = Compose $ Just xs

len :: [a] -> Const Int a
len = genericLength

safeInit :: [a] -> [a]
safeInit [] = []
safeInit xs = init xs

safeHead :: [a] -> Maybe a
safeHead = fmap fst . uncons

safeLast :: [a] -> Maybe a
safeLast = getLast . foldMap (Last . Just)

safeLast' :: [a] -> Sum Identity (Const ()) a
safeLast' = maybe (InR (Const ())) (InL . Identity) . safeLast

unsnoc :: [a] -> Maybe ([a], a)
unsnoc = foldr f Nothing where
  f a Nothing = Just ([], a)
  f a (Just (xs, x)) = Just (a:xs, x)

unsnoc' :: [a] -> Sum (Const ()) (Product [] Identity) a
unsnoc' = maybe (InL (Const ())) (InR . uncurry Pair . coerce) . unsnoc
-- unsnoc' :: [a] -> Compose Maybe (Product [] Identity) a
-- unsnoc' = Compose . fmap (uncurry Pair . coerce) . unsnoc

uncons :: [a] -> Maybe (a, [a])
uncons []     = Nothing
uncons (x:xs) = Just (x, xs)

uncons' :: [a] -> Sum (Const ()) (Product Identity []) a
uncons' = maybe (InL (Const ())) (InR . uncurry Pair . coerce) . uncons

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

------ Functions as Folds ------

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

-- -- This works as expected when calling
-- -- >> optimize Lexicographic revMinFold
-- -- Only shapes are minimized
-- revMinFold :: ConstraintSet
-- revMinFold = do
--   f <- symbolicMorphism "u" "g"

--   let
--     make :: SymVal a => String -> [a] -> ConstraintSet
--     make s xs = makeMinFoldr @Identity @[] @(Const ())
--       (Const ()) (Identity <$> xs) [] (reverse xs) f ("rev_" <> s)

--   make @Integer "4567" [4,5,6,7]
--   make @Bool "TF" [True, False]

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


------ Shape Completeness ------

recCalls :: Functor f => Mono c (Compose [] f) -> [[f ()]]
recCalls = tails . simplify

simplify :: Functor f => Mono c (Compose [] f) -> [f ()]
simplify (Mono (Compose xs)) = map (() <$) xs

isShapeComplete :: (Functor f, Eq (f ())) => [Mono c (Compose [] f)] -> Bool
isShapeComplete xs =
  let subShapes = concatMap recCalls xs
  in all (`elem` map simplify xs) subShapes

isShapeComplete' :: [Mono c []] -> Bool
isShapeComplete' = isShapeComplete @Identity . map (mapMono coerce)

type Cont f = (Functor f, Foldable f, Eq (f ()), Ord (f ()))

extract :: Cont f => f a -> (f (), [a])
extract x = (() <$ x, toList x)

single :: (Cont f, Cont g, Ord a) => f a -> g a -> (f (), Maybe (g (), [Set Int]))
single i o = (s, Just (t, r <$> q))
  where
    (s, p) = extract i
    (t, q) = extract o
    m = Map.fromListWith (<>) (zip p (Set.singleton <$> [0 :: Int ..]))
    r x = maybe mempty id $ Map.lookup x m

-- data Mono' c f where
--   Mono' :: c a => f a -> Mono' c f

-- mapMono' :: (forall a. f a -> g a) -> Mono' f -> Mono' g
-- mapMono' f (Mono @a x) = Mono @a (f x)

realizable :: (Cont f, Cont g) => [Mono Ord (Product f g)] -> Bool
realizable xs = all (maybe False (all (not . null) . snd)) zs
  where
    ys = (\(Mono (Pair f g)) -> single f g) <$> xs
    zs = Map.fromListWith foo ys
    foo x y = do
      (a, as) <- x
      (b, bs) <- y
      guard (a == b)
      let cs = zipWith Set.intersection as bs
      return (a, cs)
