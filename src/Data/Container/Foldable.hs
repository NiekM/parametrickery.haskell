{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Container.Foldable where

import Data.Foldable
import Data.List ((!?))
import Map qualified
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.List (genericLength)
import Data.List.NonEmpty qualified as NonEmpty

import Base
import Constraint
import Data.Mono

class (Functor f, Foldable f, Ord1 f, Eq1 f) => Container f
instance (Functor f, Foldable f, Ord1 f, Eq1 f) => Container f

type Example f g = Mono Ord (Product f g)

{-# COMPLETE Example #-}
pattern Example :: () => forall a. Ord a => f a -> g a -> Example f g
pattern Example input output = Mono (Pair input output)

type Shape f = f ()

shape :: Functor f => f a -> Shape f
shape = (() <$)

-- A monomorphic input-output example (i.e. translated to the container setting)
-- type Monomorphic f g = (Shape f, (Shape g, [Set Natural]))

-- A set of monomorphic input-output examples (i.e. a partial container
-- morphism)
type Morph f g = Map (Shape f) (Shape g, [Set Natural])

indices :: Ord a => [a] -> Map a (Set Natural)
indices xs = Map.fromListWith' (Set.fromList . toList) $ zip xs [0..]
-- indices = Map."inverse" . Map.fromList . zip [0..]

-- Turn an example into its monomorphic form.
monomorphise :: (Container f, Container g) => Example f g -> Morph f g
monomorphise (Example i o) = Map.singleton s (t, origin <$> q)
  where
    s = shape i; p = toList i; t = shape o; q = toList o
    origin n = Map.lookupDefault n Set.empty $ indices p

merge :: (Container f, Container g) => [Morph f g] -> Maybe (Morph f g)
merge = Map.unionsWithA \ys -> do
  let (ss, ps) = NonEmpty.unzip ys
  s <- allSame ss
  p <- consistent ps
  return (s, p)

fromExamples :: (Container f, Container g) => [Example f g] -> Maybe (Morph f g)
fromExamples = merge . map monomorphise

consistent :: Ord a => NonEmpty [Set a] -> Maybe [Set a]
consistent = traverse nonEmpty . foldl1 (zipWith Set.intersection)

type List = Compose []

sketchMap :: [Example (List f) (List g)] -> Maybe [Example f g]
sketchMap = fmap concat . traverse
  \(Example (Compose xs) (Compose ys)) -> pairUpWith Example xs ys

type FoldIn c d f = Product (Product c d) (List f)

data FoldRes c d f g = FoldRes
  { algebra :: Maybe (Morph (Sum (Product (Product c f) g) d) g)
  , missing :: [Shape (FoldIn c d f)]
  }
-- TODO: add pretty printing for FoldRes, which nicely prints the partial
-- morphism if satisfiable, as well as reporting missing inputs.

deriving instance All Eq1   [c, d, f, g] => Eq   (FoldRes c d f g)
deriving instance All Ord1  [c, d, f, g] => Ord  (FoldRes c d f g)
deriving instance All Show1 [c, d, f, g] => Show (FoldRes c d f g)
deriving instance (All Read1 [c, d, f, g], All Ord1 [c, d, f, g])
  => Read (FoldRes c d f g)

-- This function
-- 1. computes a subset of complete traces;
-- 2. propagates this subset through foldr;
-- 3. returns a normalized partial morphism if it is realizable;
-- 4. reports any missing inputs.
-- TODO: refactor this all a bit
sketchFoldr :: All Container [c, d, f, g]
  => Morph (FoldIn c d f) g -> FoldRes c d f g
sketchFoldr m = Map.toList m & uncurry FoldRes . first merge . partitionWith
  \(s, (t, p)) -> case s of
    Pair (Pair _ d) (Compose []) -> Left $ Map.singleton (InR d) (t, p)
    Pair ctx@(Pair c _) (Compose (x:xs))    ->
      case Map.lookup (Pair ctx (Compose xs)) m of
        Nothing     -> Right . Pair ctx $ Compose xs
        Just (u, q) -> Left $ Map.singleton (InL (Pair (Pair c x) u))
          (t, substitute (remap x (Compose xs) q) p)

sketchFoldr' :: All Container [f, g]
  => Morph (List f) g
  -> FoldRes (Const ()) (Const ()) f g
sketchFoldr' = sketchFoldr .
  Map.mapKeysMonotonic (Pair $ Pair (Const ()) (Const ()))

-- Computes a remapping of positions based on the input shape and the positions
-- of the recursive call.
remap :: Foldable f => Shape f -> Shape (List f)
  -> [Set Natural] -> Map Natural (Set Natural)
remap s (Compose xs) ps = Map.fromSet bar positions
  where
    positions :: Set Natural
    positions = Set.fromList [0.. fromIntegral (length (Compose (s:xs))) - 1]

    i :: Natural
    i = fromIntegral (length s)

    bar :: Natural -> Set Natural
    bar n
      | n < i = Set.singleton n
      | otherwise =
        Set.fromList . map fst . filter (Set.member (n - i) . snd) $
        zip [i..] ps

substitute :: Map Natural (Set Natural) -> [Set Natural] -> [Set Natural]
substitute m = map . unionMap $ \n -> Map.lookupDefault n Set.empty m

------ Utils ------

allSame :: Eq a => NonEmpty a -> Maybe a
allSame (x :| xs)
  | all (== x) xs = Just x
  | otherwise     = Nothing

nonEmpty :: Set a -> Maybe (Set a)
nonEmpty x
  | null x    = Nothing
  | otherwise = Just x

partitionWith :: (a -> Either b c) -> [a] -> ([b], [c])
partitionWith f = ([], []) & foldr \x -> case f x of
  Left  a -> first  (a:)
  Right b -> second (b:)

-- concatMap for Sets
unionMap :: (Ord a, Ord b) => (a -> Set b) -> Set a -> Set b
unionMap f = Set.unions . Set.map f

-- A version of zip that requires the lists to match up
pairUpWith :: (a -> b -> c) -> [a] -> [b] -> Maybe [c]
pairUpWith f xs ys
  | length xs == length ys = Just $ zipWith f xs ys
  | otherwise              = Nothing

------ Examples ------

example :: forall a f g. Ord a => f a -> g a -> Example f g
example = Example

simpleInputs :: [Mono Ord []]
simpleInputs =
  [ Mono @Integer []
  , Mono @Integer [1]
  , Mono @Integer [2,3]
  , Mono @Integer [4,5,6]
  ]

simpleBench :: (forall a. [a] -> f a) -> [Example (List Identity) f]
simpleBench model = simpleInputs <&> \(Mono @a xs) ->
  example @a (coerce xs) (model xs)

tailExample, initExample, revExample :: [Example (List Identity) []]
tailExample = simpleBench \case { [] -> []; _:xs -> xs }
initExample = simpleBench \case { [] -> []; xs -> init xs }
revExample  = simpleBench reverse

headExample, lastExample :: [Example (List Identity) Maybe]
headExample = simpleBench \case { [] -> Nothing; x:_  -> Just x }
lastExample = simpleBench \case { [] -> Nothing; xs -> Just (last xs) }

lengthExample :: [Example (List Identity) (Const Int)]
lengthExample = simpleBench genericLength

nullExample :: [Example (List Identity) (Const Bool)]
nullExample = simpleBench $ Const . null

intInputs :: [Mono Ord (Product (Const Int) [])]
intInputs = [0, 1, 2] >>= \n -> simpleInputs <&> mapMono (Pair (Const n))

intBench :: (forall a. Int -> [a] -> f a) ->
  [Example (FoldIn (Const Int) (Const Int) Identity) f]
intBench model = intInputs <&> \(Mono @a (Pair (Const i) xs)) ->
  example @a (Pair (Pair (Const i) (Const i)) (coerce xs)) (model i xs)

dropExample, takeExample ::
  [Example (FoldIn (Const Int) (Const Int) Identity) []]
dropExample = intBench drop
takeExample = intBench take

indexExample :: [Example (FoldIn (Const Int) (Const Int) Identity) Maybe]
indexExample = intBench (flip (!?))

splitAtExample ::
  [Example (FoldIn (Const Int) (Const Int) Identity) (Product [] [])]
splitAtExample = intBench $ (uncurry Pair .) . splitAt

newtype Dup a = Dup { unDup :: (a, a) }
  deriving newtype (Eq, Ord)
  deriving stock (Show, Functor)

instance Foldable Dup where
  foldMap f (Dup (x, y)) = f x <> f y

instance Eq1 Dup where
  liftEq eq (Dup (x, y)) (Dup (z, w)) = eq x z && eq y w

instance Ord1 Dup where
  liftCompare cmp (Dup (x, y)) (Dup (z, w)) = cmp x z <> cmp y w

-- TODO: unzip fails, but it should be satisfiable, right?
-- figure out what goes wrong
unzipExample :: [Example (List Dup) (Product [] [])]
unzipExample =
  [ example @Integer (Compose []) (Pair [] [])
  , example @Integer (Compose [Dup (1,2)]) (Pair [1] [2])
  -- , example @Integer (Compose [Dup (1,2)]) (Pair [1,1,1,1] [])
  , example @Integer (Compose [Dup (1,2), Dup (3,4)]) (Pair [1,3] [2,4])
  , example @Integer
    (Compose [Dup (1,2), Dup (3,4), Dup (5,6)]) (Pair [1,3,5] [2,4,6])
  ]

triExample :: [Example [] Identity]
triExample =
  [ example @Integer [0, 0, 1] 0
  , example @Integer [0, 1, 0] 0
  , example @Integer [1, 0, 0] 0
  ]

-- >>> fromExamples triExample
-- Nothing

-- >>> fromExamples =<< sketchMap revExample

-- >>> fromExamples revExample
-- Just (fromList [(Compose [Identity (),Identity (),Identity ()],(Compose [Identity (),Identity (),Identity ()],[fromList [2],fromList [1],fromList [0]]))])

-- >>> fromExamples revExample <&> sketchFoldr
-- Just (Just (fromList [(Pair (Identity ()) (Compose []),(Compose [Identity ()],[fromList [0]])),(Pair (Identity ()) (Compose [Identity ()]),(Compose [Identity (),Identity ()],[fromList [1],fromList [0]])),(Pair (Identity ()) (Compose [Identity (),Identity ()]),(Compose [Identity (),Identity (),Identity ()],[fromList [1],fromList [2],fromList [0]]))]),[])

-- >>> fromExamples tailExample <&> sketchFoldr
-- Just (Nothing,[])

-- >>> fromExamples unzipExample <&> sketchFoldr
-- Just (Just (fromList [(Pair (Dup {unDup = ((),())}) (Pair [] []),(Pair [()] [()],[fromList [0],fromList [1]])),(Pair (Dup {unDup = ((),())}) (Pair [()] [()]),(Pair [(),()] [(),()],[fromList [0],fromList [2],fromList [1],fromList [3]])),(Pair (Dup {unDup = ((),())}) (Pair [(),()] [(),()]),(Pair [(),(),()] [(),(),()],[fromList [0],fromList [2],fromList [3],fromList [1],fromList [4],fromList [5]]))]),[])
