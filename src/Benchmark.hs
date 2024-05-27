{-# LANGUAGE TypeAbstractions #-}

module Benchmark where

import Data.List ((!?))

import Data.SBV

import Base
import Data.Container
import Data.Mono
import Sketch.Foldr

type Mono' = Mono SymVal

simpleInputs :: [Mono' []]
simpleInputs =
  [ Mono @Integer [1,2,3]
  , Mono          [True, False]
  , Mono          [()]
  ]

dropInputs :: [(Int, Mono' [])]
dropInputs = [(1,),(2,)] >>= (<$> simpleInputs)

split :: Mono' [] -> [Mono' (Product [] [])]
split (Mono @a xs) = Mono @a . uncurry Pair <$> splits
  where
    splits :: [([a],[a])]
    splits = flip splitAt xs <$> [0 .. length xs]

-- For functions of the form `foldr f e`
simple :: Container g => (forall a. [a] -> g a) -> FoldExamples
simple f = FoldExamples @_ @_ @Identity $
  simpleInputs <&> mapMono \xs ->
    FoldExample (Const ()) (Const ()) (coerce xs) (f xs)

withInt :: Container g => (forall a. Int -> [a] -> g a) -> FoldExamples
withInt f = FoldExamples @_ @_ @Identity $
  dropInputs <&> \(n, Mono @a xs) ->
    Mono @a (Pair (Pair (Pair (Const n) (Const n)) (coerce xs)) (f n xs))

withList :: Container g => (forall a. [a] -> [a] -> g a) -> FoldExamples
withList f = FoldExamples @_ @_ @Identity $ twoInputs <&> mapMono
  \(Pair xs ys) -> Pair (Pair (Pair (Const ()) xs) (coerce ys)) (f xs ys)

listInputs :: [Mono' []]
listInputs =
  [ Mono @Integer [1,2,3]
  , Mono          [True, False]
  , Mono          [()]
  , Mono @Integer []
  ]

splitInputs :: [Mono' (Product [] [])]
splitInputs = concatMap split listInputs

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

dupInputs :: [Mono' (Compose [] Dup)]
dupInputs = Mono @Integer . Compose . map Dup <$>
  [ []
  , [(1,2)]
  , [(1,2), (3,4)]
  , [(1,2), (3,4), (5,6)]
  ]

nested :: forall f g. (Container f, Container g) =>
  (forall a. [f a] -> g a) -> [Mono' (Compose [] f)] -> FoldExamples
nested f inputs = FoldExamples @(Const ()) @(Const ()) @f @g $ inputs <&>
  mapMono \xs -> Pair (Pair (Pair (Const ()) (Const ())) xs) (f $ getCompose xs)

preludeBenches :: [(String, FoldExamples)]
preludeBenches =
  [ ("null"     , simple _null)
  , ("length"   , simple _length)
  , ("head"     , simple safeHead)
  , ("last"     , simple safeLast)
  , ("tail"     , simple safeTail)
  , ("init"     , simple safeInit)
  , ("reverse"  , simple reverse)
  , ("index"    , withInt index)
  , ("drop"     , withInt drop)
  , ("take"     , withInt take)
  , ("splitAt"  , withInt _splitAt)
  , ("append"   , withList append)
  , ("prepend"  , withList prepend)
  , ("zip"      , withList _zip)
  , ("unzip"    , nested _unzip dupInputs)
  , ("concat"   , nested concat nestedInputs)
  ] where

    append :: [a] -> [a] -> [a]
    append  = (++)

    prepend :: [a] -> [a] -> [a]
    prepend = flip (++)

    safeHead :: [a] -> Maybe a
    safeHead []    = Nothing
    safeHead (x:_) = Just x

    safeLast :: [a] -> Maybe a
    safeLast []    = Nothing
    safeLast xs    = Just $ last xs

    index :: Int -> [a] -> Maybe a
    index n xs = xs !? n

    _null :: [a] -> Const Bool a
    _null = Const . null

    _length :: [a] -> Const Int a
    _length = Const . length

    safeTail :: [a] -> [a]
    safeTail []     = []
    safeTail (_:xs) = xs

    safeInit :: [a] -> [a]
    safeInit []     = []
    safeInit xs     = init xs

    _splitAt :: Int -> [a] -> ListPair a
    _splitAt n xs = ListPair $ splitAt n xs

    _zip :: [a] -> [a] -> PairList a
    _zip xs ys = PairList $ zip xs ys

    _unzip :: [Dup a] -> ListPair a
    _unzip = ListPair . unzip . coerce

incompleteBenches :: [(String, FoldExamples)]
incompleteBenches = preludeBenches <&> fmap \(FoldExamples examples) ->
  FoldExamples (decimate examples)

-- Used to make sets incomplete.
decimate :: [a] -> [a]
decimate [] = []
decimate [x] = [x]
decimate (_:x:xs) = x : decimate xs

-- maybeTailInit :: [(String, FoldExamples)]
-- maybeTailInit =
--   [ ("tail", simple t)
--   , ("init", simple i)
--   ] where
--     t, i :: [a] -> OptList a
--     t [] = OptList Nothing
--     t (_:xs) = OptList $ Just xs
--     i [] = OptList Nothing
--     i xs = OptList . Just $ init xs
 