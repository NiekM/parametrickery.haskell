{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoStarIsType #-}

module Data.Container.Foldable where

import GHC.TypeLits
import Data.Foldable
import Data.Bifunctor (bimap)
import Data.List (intercalate)
import Control.Monad.State
import Data.Map.Utils qualified as Map
import Data.Map.Multi (Multi)
import Data.Map.Multi qualified as Multi
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.List.NonEmpty qualified as NonEmpty

import Base
import Constraint
import Data.Mono
import Data.Dup
import Data.Functor.Context
import Pretty

class    (Functor f, Foldable f, Traversable f, Ord1 f, Eq1 f) => Container f
instance (Functor f, Foldable f, Traversable f, Ord1 f, Eq1 f) => Container f

type Example f g = Mono Ord (Product f g)

{-# COMPLETE Example #-}
pattern Example :: () => forall a. Ord a => f a -> g a -> Example f g
pattern Example input output = Mono (Pair input output)

type Shape f = f ()

shape :: Functor f => f a -> Shape f
shape = (() <$)

type Positions = Map Natural 

positions :: Foldable f => f a -> Positions a
positions = Map.fromList . zip [0..] . toList

-- i.e. a position morphism.
type Origins = Multi Natural Natural

origins :: Ord a => Positions a -> Positions a -> Origins
origins p q = Multi.remapping (Multi.fromMap q) (Multi.fromMap p)
--q <&> \x -> Map.lookupDefault x Set.empty $ Map.inverse p

-- compose :: Origins -> Origins -> Origins
-- compose p = fmap $ foldMap \n -> Map.lookupDefault n Set.empty p

-- A partial container morphism
type Morph f g = Map (Shape f) (Shape g, Origins)

-- indices :: Ord a => [a] -> Map a (Set Natural)
-- indices xs = Map.fromListWith' (Set.fromList . toList) $ zip xs [0..]
-- indices = Map."inverse" . Map.fromList . zip [0..]

-- Turn an example into its monomorphic form.
toMorph :: (Container f, Container g) => Example f g -> Morph f g
toMorph (Example i o) = Map.singleton s (t, origins p q)
  where
    s = shape i; p = positions i; t = shape o; q = positions o
    -- origin n = Map.lookupDefault n Set.empty $ indices p

merge :: (Container f, Container g) => [Morph f g] -> Maybe (Morph f g)
merge = Map.unionsWithA \ys -> do
  let (ss, ps) = NonEmpty.unzip ys
  s <- allSame ss
  p <- consistent ps
  return (s, p)

fromExamples :: (Container f, Container g) => [Example f g] -> Maybe (Morph f g)
fromExamples = merge . map toMorph

-- consistent :: Ord a => NonEmpty [Set a] -> Maybe [Set a]
-- consistent = traverse nonEmpty . foldl1 (zipWith Set.intersection)

consistent :: NonEmpty Origins -> Maybe Origins
consistent = Multi.consistent . foldl1 Multi.intersection

type List = Compose []

sketchMap :: [Example (List f) (List g)] -> Maybe [Example f g]
sketchMap = fmap concat . traverse
  \(Example (Compose xs) (Compose ys)) -> pairUpWith Example xs ys

newtype Var = Var Natural
  deriving newtype (Eq, Ord, Enum)

instance Show Var where
  show v = (pure <$> "abcdghijklmnopqrstuvwxyz") !! fromEnum v

newtype Vars = Vars { getVars :: Set Var }
  deriving newtype (Eq, Ord)

instance Show Vars where
  show (Vars xs) = case Set.toList xs of
    [x] -> show x
    ys  -> ("{"++) . (++"}") . intercalate ", " . map show $ ys

recoverInput :: Traversable f => Shape f -> f Var
recoverInput s = populate s [Var 0 ..]

recoverOutput :: Traversable f => Shape f -> Origins -> f Vars
recoverOutput t q = populate t $ map (Vars . Set.mapMonotonic Var)
  (Multi.elems q)

rmp :: All Container [ctx, f] => Shape ctx -> Shape f -> Origins -> Origins
rmp ctx hd rec_p =
  Multi.inverse $ Multi.union
  (positions (Pair ctx hd) & Multi.fromMap . Map.mapWithKey \k _ -> k)
  (Multi.compose mid_old new_mid)
  where
    len = fromIntegral $ length ctx + length hd
    new_mid = rec_p & Multi.mapKeysMonotonic (+ len)
    mid_old = Multi.fromMap $ (Set.unions $ Multi.elems new_mid) & Map.fromSet
      \k -> if k < fromIntegral (length ctx)
        then k
        else k + fromIntegral (length hd)


-- substitute :: Map Natural (Set Natural) -> [Set Natural] -> [Set Natural]
-- substitute m = map $ foldMap \n -> Map.lookupDefault n Set.empty m

------ Contexts ------

type FoldrIn  ctx f = Product (Context ctx) (List f)
type FoldrEx  ctx f g = Morph (FoldrIn ctx f) g
type FoldrAlg ctx f g =
  Morph (Product (Context ctx) (Sum (Product f g) (Const ()))) g

-- TODO: use some monad with MonadWriter (for missing inputs) and MonadError
-- (for unrealizability)
foldrSketch :: All Container [Context ctx, f, g]
  => FoldrEx ctx f g -> Maybe (FoldrAlg ctx f g)
foldrSketch m = Map.toList m & merge . fst . partitionWith
  \(s, (t, p)) -> case s of
    Pair ctx (Compose []) ->
      Left $ Map.singleton (Pair ctx (InR (Const ()))) (t, p)
    Pair ctx (Compose (x:xs)) ->
      case Map.lookup (Pair ctx (Compose xs)) m of
        -- TODO: don't just throw away these results
        Nothing     -> Right . Pair ctx $ Compose xs
        Just (u, q) -> Left $ Map.singleton (Pair ctx (InL (Pair x u)))
          (t, Multi.compose (rmp ctx x q) p)

printBench :: [Container, Pretty] ** [Context ctx, f, g]
  => Maybe (FoldrAlg ctx f g) -> IO ()
printBench = \case
  Nothing -> putStrLn "Unsatisfiable."
  Just xs -> do
    putStrLn "Satisfiable."
    putStrLn ""
    putStrLn $ pp xs

pp :: [Container, Pretty] ** [Context ctx, f, g] => FoldrAlg ctx f g -> String
pp = ("foldr f e\n  where" ++)
  . concatMap
    ( \(ctx, (fs, es)) ->
      -- TODO: use recoverinput on ctx and input combined.
      -- probably best to do before anything else
      ("\n    " ++) $ pretty 0 ctx $
        concatMap ("\n      " ++) $
          ( fs <&> \(Pair x r, (t, q)) -> "f " <> pretty 11 x
              (" " <> pretty 11 r (" = " <> pretty 0 (recoverOutput t q) ""))
              -- (" " <> pretty 11 r (" = " <> pretty 0 (recoverOutput t q) (show q)))
          ) ++
          ( es <&> \(_, (t, q)) -> "e = " <> pretty 0 (recoverOutput t q) ""
          )
    )
  . Map.toList
  . fmap
    ( bimap Map.toList Map.toList
    . Map.splitEither
    . Map.mapKeysMonotonic \case { InL x -> Left x; InR y -> Right y }
    )
  . Map.curry
  . Map.mapKeysMonotonic \case { Pair x y -> (x, y) }
  . Map.mapKeysMonotonic recoverInput

------ Benchmarks ------

type Inputs f = [Mono Ord f]

simpleInputs :: Inputs []
simpleInputs =
  [ Mono @Integer []
  , Mono @Integer [1]
  , Mono @Integer [2,3]
  , Mono @Integer [4,5,6]
  ]

type Number = '["n" :-> Const Int]

intInputs :: Inputs (FoldrIn Number Identity)
intInputs = [0 :: Int, 1, 2] >>= \n -> simpleInputs <&> mapMono
  (Pair (Cons (Const n) Nil) . coerce)

argInputs :: Inputs (Product Identity [])
argInputs =
  [ Mono @Integer $ Pair 0 []
  , Mono @Integer $ Pair 0 [1]
  , Mono @Integer $ Pair 0 [2,3]
  , Mono @Integer $ Pair 0 [4,5,6]
  ]

dupInputs :: Inputs (List Dup)
dupInputs =
  [ Mono @Integer (Compose [])
  , Mono @Integer (Compose [Dup (1,2)])
  , Mono @Integer (Compose [Dup (1,2), Dup (3,4)])
  , Mono @Integer (Compose [Dup (1,2), Dup (3,4), Dup (5,6)])
  ]

simpleBench :: Container f => (forall a. [a] -> f a) ->
  Maybe (FoldrAlg '[] Identity f)
simpleBench model = foldrSketch =<< fromExamples do
  simpleInputs <&> mapMono \xs -> Pair (Pair Nil (coerce xs)) (model xs)

intBench :: Container f => (forall a. Int -> [a] -> f a) ->
  Maybe (FoldrAlg Number Identity f)
intBench model = foldrSketch =<< fromExamples do
  intInputs <&> mapMono \input@(Pair (Cons n Nil) xs) ->
    Pair input $ model (coerce n) (coerce xs)

argBench :: Container f => (forall a. a -> [a] -> f a) ->
  Maybe (FoldrAlg '["x" :-> Identity] Identity f)
argBench model = foldrSketch =<< fromExamples do
  argInputs <&> mapMono \(Pair x xs) -> do
    Pair (Pair (Cons x Nil) (coerce xs)) $ model (coerce x) xs

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

-- A version of zip that requires the lists to match up
pairUpWith :: (a -> b -> c) -> [a] -> [b] -> Maybe [c]
pairUpWith f xs ys
  | length xs == length ys = Just $ zipWith f xs ys
  | otherwise              = Nothing

populate :: Traversable f => f a -> [b] -> f b
populate m = evalState $ m & traverse \_ ->
  get >>= \case
    [] -> error "Not enough values"
    x:xs -> do
      put xs
      return x

-- TODO: check if snoc is actually propagated correctly...
--   it seems wrong 
snoc :: a -> [a] -> [a]
snoc x xs = xs ++ [x]
