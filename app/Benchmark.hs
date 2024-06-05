{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

module Benchmark where

import Prelude hiding
  (null, length, head, last, tail, init, splitAt, zip, unzip)
import Prelude qualified

import Data.Functor ((<&>))
import Data.Functor.Product
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Functor.Const
import Data.List ((!?))
import Data.Coerce

import Data.SBV

import Data.Container
import Data.Mono
import Sketch.Foldr

type Mono' = Mono SymVal

-- | Basic list inputs.
listInputs :: [Mono' []]
listInputs =
  [ Mono @Integer [1,2,3]
  , Mono          [True, False]
  , Mono          [()]
  , Mono @Integer []
  ]

-- | Create a benchmark based on a simple function of type @[a] -> g a@.
simple :: Container g => (forall a. [a] -> g a) -> FoldExamples
simple f = FoldExamples @_ @Identity $
  listInputs <&> mapMono \xs ->
    FoldExample (Const ()) (coerce xs) (f xs)

-- | Basic list inputs with an additional integer argument.
inputsWithInt :: [(Int, Mono' [])]
inputsWithInt = [(1,),(2,)] >>= (<$> listInputs)

-- | Create a benchmark based on a function of type @Int -> [a] -> g a@.
withInt :: Container g => (forall a. Int -> [a] -> g a) -> FoldExamples
withInt f = FoldExamples @_ @Identity $
  inputsWithInt <&> \(n, Mono @a xs) ->
    Mono @a (Pair (Pair (Const n) (coerce xs)) (f n xs))

-- | Pairs of lists as inputs.
twoInputs :: [Mono' (Product [] [])]
twoInputs = Mono @Integer <$>
  [ Pair [] []
  , Pair [] [1]
  , Pair [1] []
  , Pair [1] [2]
  , Pair [1] [2,3]
  , Pair [1,2] []
  , Pair [1,2] [3]
  , Pair [1,2] [3,4]
  ]

-- | Create a benchmark based on a function of type @[a] -> [a] -> g a@.
withList :: Container g => (forall a. [a] -> [a] -> g a) -> FoldExamples
withList f = FoldExamples @_ @Identity $ twoInputs <&> mapMono
  \(Pair xs ys) -> Pair (Pair xs (coerce ys)) (f xs ys)

-- | Nested lists as inputs.
nestedInputs :: [Mono' (Compose [] [])]
nestedInputs = Mono @Integer . Compose <$>
  [ []
  , [[]]
  , [[1]]
  , [[1,2]]
  , [[],[]]
  , [[1],[2]]
  , [[1,2],[3]]
  , [[1],[2,3]]
  , [[1],[2],[1]]
  ]

-- | Pairs of lists as inputs.
dupInputs :: [Mono' (Compose [] Dup)]
dupInputs = Mono @Integer . Compose . map Dup <$>
  [ []
  , [(1,2)]
  , [(1,2), (3,4)]
  , [(1,2), (3,4), (5,6)]
  ]

-- | Create a benchmark based on a function of type @[f a] -> g a@.
nested :: forall f g. (Container f, Container g) =>
  (forall a. [f a] -> g a) -> [Mono' (Compose [] f)] -> FoldExamples
nested f inputs = FoldExamples @(Const ()) @f @g $ inputs <&>
  mapMono \xs -> Pair (Pair (Const ()) xs) (f $ getCompose xs)

type Benchmark = [(String, FoldExamples)]

shapeComplete :: Benchmark
shapeComplete =
  [ ("null"     , simple null)
  , ("length"   , simple length)
  , ("head"     , simple head)
  , ("last"     , simple last)
  , ("tail"     , simple tail)
  , ("init"     , simple init)
  , ("reverse"  , simple reverse)
  , ("index"    , withInt index)
  , ("drop"     , withInt drop)
  , ("take"     , withInt take)
  , ("splitAt"  , withInt splitAt)
  , ("append"   , withList append)
  , ("prepend"  , withList prepend)
  , ("zip"      , withList zip)
  , ("unzip"    , nested unzip dupInputs)
  , ("concat"   , nested concat nestedInputs)
  ] where

    -- Functions with monomorphic output.

    null :: [a] -> Const Bool a
    null = Const . Prelude.null

    length :: [a] -> Const Int a
    length = Const . Prelude.length

    -- Partial functions.

    safeMaybe :: ([a] -> b) -> [a] -> Maybe b
    safeMaybe _ [] = Nothing
    safeMaybe f xs = Just $ f xs

    safeList :: ([a] -> [b]) -> [a] -> [b]
    safeList _ [] = []
    safeList f xs = f xs

    head :: [a] -> Maybe a
    head = safeMaybe Prelude.head

    last :: [a] -> Maybe a
    last = safeMaybe Prelude.last

    tail :: [a] -> [a]
    tail = safeList Prelude.tail

    init :: [a] -> [a]
    init = safeList Prelude.init

    -- Operators.

    index :: Int -> [a] -> Maybe a
    index = flip (!?)

    append :: [a] -> [a] -> [a]
    append  = (++)

    prepend :: [a] -> [a] -> [a]
    prepend = flip (++)

    -- Functions with specialized containers.

    splitAt :: Int -> [a] -> ListPair a
    splitAt n xs = ListPair $ Prelude.splitAt n xs

    zip :: [a] -> [a] -> PairList a
    zip xs ys = PairList $ Prelude.zip xs ys

    unzip :: [Dup a] -> ListPair a
    unzip = ListPair . Prelude.unzip . coerce

-- | A shape incomplete version of the benchmark, with every other input removed
-- from each set of input-output examples.
shapeIncomplete :: Benchmark
shapeIncomplete = shapeComplete <&> fmap \(FoldExamples examples) ->
  FoldExamples (decimate examples)

-- | Removes every other element from a list.
decimate :: [a] -> [a]
decimate [] = []
decimate [x] = [x]
decimate (_:x:xs) = x : decimate xs
