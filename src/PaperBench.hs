{-# LANGUAGE TypeAbstractions #-}

module PaperBench where

import Data.List ((!?))

import Data.SBV

import Base
import Data.Container
import Data.Mono
import Sketch.Foldr

-- Functions from Prelude:
-- concat
-- (++)*    *(append, prepend)
-- PARTIAL: head, last, tail, init, (!!)
-- null, length, reverse
-- take, drop, splitAt
-- SINGLE POLY: zip, unzip

-- _concat :: [[a]] -> [a]
-- _concat = concat

type Mono' = Mono SymVal

append, prepend :: [a] -> [a] -> [a]
append  = (++)
prepend = flip (++)

_head, _last :: [a] -> Maybe a
_head []    = Nothing
_head (x:_) = Just x
_last []    = Nothing
_last xs    = Just $ last xs

index :: Int -> [a] -> Maybe a
index n xs = xs !? n

_null :: [a] -> Const Bool a
_null = Const . null

_length :: [a] -> Const Int a
_length = Const . length

_tail, _init :: [a] -> [a]
_tail []     = []
_tail (_:xs) = xs
_init []     = []
_init xs     = init xs

-- ListPair works, but `Product [] []` does not...
_splitAt :: Int -> [a] -> ListPair a
_splitAt n xs = ListPair $ splitAt n xs

_zip :: [a] -> [a] -> PairList a
_zip xs ys = PairList $ zip xs ys

-- NOTE: works, but needs a bit more resources, just like splitAt
_unzip :: [Dup a] -> ListPair a
_unzip = ListPair . unzip . coerce

tailInputs :: [Mono' []]
tailInputs =
  [ Mono @Integer [1,2,3]
  , Mono          [True, False]
  , Mono          [()]
  ]

dropInputs :: [(Int, Mono' [])]
dropInputs = [(1,),(2,)] >>= (<$> tailInputs)

split :: Mono' [] -> [Mono' (Product [] [])]
split (Mono @a xs) = Mono @a . uncurry Pair <$> splits
  where
    splits :: [([a],[a])]
    splits = flip splitAt xs <$> [0 .. length xs]

-- For functions of the form `foldr f e`
tailLike :: Container g => (forall a. [a] -> g a) -> FoldInputs
tailLike f = FoldInputs @_ @_ @Identity $
  tailInputs <&> mapMono \xs ->
    FoldInput (Const ()) (Const ()) (coerce xs) (f xs)

dropLike :: Container g => (forall a. Int -> [a] -> g a) -> FoldInputs
dropLike f = FoldInputs @_ @_ @Identity $
  dropInputs <&> \(n, Mono @a xs) ->
    Mono @a (Pair (Pair (Pair (Const n) (Const n)) (coerce xs)) (f n xs))

zipLike :: Container g => (forall a. [a] -> [a] -> g a) -> FoldInputs
zipLike f = FoldInputs @_ @_ @Identity $ twoInputs <&> mapMono
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
twoInputs =
  [ Mono @Integer $ Pair [] []
  , Mono @Integer $ Pair [] [1]
  , Mono @Integer $ Pair [1] []
  , Mono @Integer $ Pair [1] [2]
  , Mono @Integer $ Pair [1] [2,3]
  , Mono @Integer $ Pair [1,2] []
  , Mono @Integer $ Pair [1,2] [3]
  , Mono @Integer $ Pair [1,2] [3,4]
  -- NOTE: it seems that this input messes it up, it's also not trace complete!
  -- , Mono @Integer $ Pair [1,2,3] [4,5,6]
  ]

nestedInputs :: [Mono' (Compose [] [])]
nestedInputs =
  [ Mono @Integer $ Compose []
  , Mono @Integer $ Compose [[]]
  , Mono @Integer $ Compose [[1]]
  , Mono @Integer $ Compose [[1,2]]
  , Mono @Integer $ Compose [[],[]]
  , Mono @Integer $ Compose [[1],[2]]
  , Mono @Integer $ Compose [[1,2],[3]]
  , Mono @Integer $ Compose [[1],[2,3]]
  , Mono @Integer $ Compose [[1],[2],[1]]
  ]

dupInputs :: [Mono' (Compose [] Dup)]
dupInputs =
  [ Mono @Integer $ Compose []
  , Mono @Integer $ Compose [Dup (1,2)]
  , Mono @Integer $ Compose [Dup (1,2), Dup (3,4)]
  -- NOTE: if we remove this larger input it does not timeout...
  , Mono @Integer $ Compose [Dup (1,2), Dup (3,4), Dup (5,6)]
  ]

nested :: forall f g. (Container f, Container g) => (forall a. [f a] -> g a) ->
  [Mono' (Compose [] f)] -> FoldInputs
nested f inputs = FoldInputs @(Const ()) @(Const ()) @f @g $ inputs <&> mapMono
  \xs -> Pair (Pair (Pair (Const ()) (Const ())) xs) (f $ getCompose xs)

preludeBenches :: [(String, FoldInputs)]
preludeBenches =
  [ ("null"     , tailLike _null)
  , ("length"   , tailLike _length)
  , ("head"     , tailLike _head)
  , ("last"     , tailLike _last)
  , ("tail"     , tailLike _tail)
  , ("init"     , tailLike _init)
  , ("reverse"  , tailLike reverse)
  , ("index"    , dropLike index)
  , ("drop"     , dropLike drop)
  , ("take"     , dropLike take)
  , ("splitAt"  , dropLike _splitAt)
  , ("append"   , zipLike append)
  , ("prepend"  , zipLike prepend)
  , ("zip"      , zipLike _zip)
  , ("unzip"    , nested _unzip dupInputs)
  , ("concat"   , nested concat nestedInputs)
  ]

incompleteBenches :: [(String, FoldInputs)]
incompleteBenches = preludeBenches <&> fmap \(FoldInputs examples) ->
  FoldInputs (decimate examples)

-- Used to make sets incomplete.
decimate :: [a] -> [a]
decimate [] = []
decimate [x] = [x]
decimate (_:x:xs) = x : decimate xs

maybeTailInit :: [(String, FoldInputs)]
maybeTailInit =
  [ ("tail", tailLike t)
  , ("init", tailLike i)
  ] where
    t, i :: [a] -> OptList a
    t [] = OptList Nothing
    t (_:xs) = OptList $ Just xs
    i [] = OptList Nothing
    i xs = OptList . Just $ init xs
 