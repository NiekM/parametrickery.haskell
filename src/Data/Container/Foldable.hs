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
import Data.List ((!?), intercalate)
import Control.Monad.State
import Map qualified
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.List (genericLength)
import Data.List.NonEmpty qualified as NonEmpty

import Base
import Constraint
import Data.Mono
import Data.Dup
import Data.Functor.Context

class    (Functor f, Foldable f, Traversable f, Ord1 f, Eq1 f) => Container f
instance (Functor f, Foldable f, Traversable f, Ord1 f, Eq1 f) => Container f

type Example f g = Mono Ord (Product f g)

{-# COMPLETE Example #-}
pattern Example :: () => forall a. Ord a => f a -> g a -> Example f g
pattern Example input output = Mono (Pair input output)

type Shape f = f ()

shape :: Functor f => f a -> Shape f
shape = (() <$)

-- A partial container morphism
type Morph f g = Map (Shape f) (Shape g, [Set Natural])

indices :: Ord a => [a] -> Map a (Set Natural)
indices xs = Map.fromListWith' (Set.fromList . toList) $ zip xs [0..]
-- indices = Map."inverse" . Map.fromList . zip [0..]

-- Turn an example into its monomorphic form.
toMorph :: (Container f, Container g) => Example f g -> Morph f g
toMorph (Example i o) = Map.singleton s (t, origin <$> q)
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
fromExamples = merge . map toMorph

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

deriving instance All Eq1          [c, d, f, g] => Eq   (FoldRes c d f g)
deriving instance All Ord1         [c, d, f, g] => Ord  (FoldRes c d f g)
deriving instance All Show1        [c, d, f, g] => Show (FoldRes c d f g)
deriving instance [Read1, Ord1] ** [c, d, f, g] => Read (FoldRes c d f g)

-- class    (Simplify f, Show (Simple f ())) => Testable f
-- instance (Simplify f, Show (Simple f ())) => Testable f

prettyRes :: Pretty c d f g => FoldRes c d f g -> String
prettyRes (FoldRes alg _mss) = case alg of
  Nothing -> "Unsatisfiable."
  Just w -> "Satisfiable.\n\n" <> pretty w <> "\n"

class Pretty c d f g where
  pretty :: Morph (Sum (Product (Product c f) g) d) g -> String

class Prtty f where
  prtty :: Show a => Int -> f a -> ShowS

  default prtty :: (Show1 f, Show a) => Int -> f a -> ShowS
  prtty = showsPrec

instance Prtty []
instance Prtty Maybe

instance Prtty Identity where
  prtty n = showsPrec n . runIdentity

instance Show k => Prtty (Const k) where
  prtty n = showsPrec n . getConst

instance (Prtty f, Prtty g) => Prtty (Product f g) where
  prtty _ (Pair x y) s = "(" <> prtty 0 x (", " <> prtty 0 y (")" <> s))

instance AllVal Prtty ctx => Prtty (Context ctx) where
  prtty _ Nil s = s
  prtty _ ctx s = '{' : intercalate ", " (strs ctx) ++ '}' : s
    where
      strs :: (AllVal Prtty c, Show a) =>
        Context c a -> [String]
      strs = \case
        Nil -> []
        Cons v x xs -> show v <> " = " <> prtty 0 x "" : strs xs

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

recoverOutput :: Traversable f => Shape f -> [Set Natural] -> f Vars
recoverOutput t q = populate t $ map (Vars . Set.mapMonotonic Var) q



-- instance (Container f, Prtty f) => Pretty (Const ()) (Const ()) Identity f where
--   pretty = printFoldr
--     . second (Map.lookup (Const ()))
--     . Map.splitEither
--     . Map.mapKeysMonotonic sumToEither
--     where
--       printFoldr (f, e) =
--         "foldr f e\n  where"
--         <> showF f
--         <> showE e

--       showF m = Map.toList m & concatMap \(s, (t, q)) -> case recoverInput s of
--         Pair (Pair _ (Identity x)) r ->
--           "\n    f " <> show x <> " " <> prtty 11 r (" = "
--             <> prtty 0 (recoverOutput t q) "")

--       showE Nothing  = "\n    e = ?"
--       showE (Just (t, q)) = "\n    e = " <> prtty 0 (recoverOutput t q) ""

--       sumToEither (InL x) = Left  x
--       sumToEither (InR y) = Right y

-- TODO: maybe we can replace c and d by Maybe c and Maybe d?
-- that way we can use the type level maybes to differentiate between using
-- contexts or not
instance [Container, Prtty] ** [c, f] => Pretty c c Identity f where
  pretty = printFoldr
    . Map.splitEither
    . Map.mapKeysMonotonic sumToEither
    where
      printFoldr (f, e) =
        "\\c -> foldr (f c) (e c)\n  where"
        <> showF f
        <> showE e

      showF m = Map.toList m & concatMap \(s, (t, q)) -> case recoverInput s of
        Pair (Pair c (Identity x)) r ->
          "\n    f " <> prtty 11 c (" " <> show x <> " " <> prtty 11 r (" = "
            <> prtty 0 (recoverOutput t q) ""))

      showE m = Map.toList m & concatMap \(s, (t, q)) ->
        "\n    e " <> prtty 11 (recoverInput s)
          (" = " <> prtty 0 (recoverOutput t q) "")
        -- case recoverInput s of
        -- i -> _
        -- case recoverInput s of
        -- Pair (Pair c (Identity x)) r ->
        --   "\n    f " <> prtty 11 c (" " <> show x <> " " <> prtty 11 r (" = "
        --     <> prtty 0 (recoverOutput t q) ""))

      -- showE Nothing  = "\n    e = ?"
      -- showE (Just (t, q)) = "\n    e = " <> prtty 0 (recoverOutput t q) ""

      sumToEither (InL x) = Left  x
      sumToEither (InR y) = Right y

-- This function
-- 1. computes a subset of complete traces;
-- 2. propagates this subset through foldr;
-- 3. returns a normalized partial morphism if it is realizable;
-- 4. reports any missing inputs.
-- TODO: refactor this all a bit
-- TODO: this is currently broken...
sketchFoldr :: All Container [c, d, f, g]
  => Morph (FoldIn c d f) g -> FoldRes c d f g
sketchFoldr m = Map.toList m & uncurry FoldRes . first merge . partitionWith
  \(s, (t, p)) -> case s of
    Pair (Pair _ d) (Compose []) -> Left $ Map.singleton (InR d) (t, p)
    Pair ctx@(Pair c _) (Compose (x:xs))    ->
      case Map.lookup (Pair ctx (Compose xs)) m of
        Nothing     -> Right . Pair ctx $ Compose xs
        Just (u, q) -> Left $ Map.singleton (InL (Pair (Pair c x) u))
          (t, substitute (remap (Pair c x) (Compose xs) q) p)

sketchFoldr' :: All Container [f, g]
  => Morph (List f) g
  -> FoldRes (Const ()) (Const ()) f g
sketchFoldr' = sketchFoldr .
  Map.mapKeysMonotonic (Pair $ Pair (Const ()) (Const ()))

-- Computes a remapping of positions based on the input shape and the positions
-- of the recursive call.
remap :: (Foldable ctx, Foldable f) => Shape (Product ctx f) -> Shape (List f)
  -> [Set Natural] -> Map Natural (Set Natural)
remap input (Compose xs) ps = Map.fromSet origins positions
  where
    positions :: Set Natural
    positions = Set.fromList [0.. fromIntegral (length input + length xs) - 1]

    i :: Natural
    i = fromIntegral (length input)

    origins :: Natural -> Set Natural
    origins n
      | n < i = Set.singleton n
      | otherwise = Set.fromList
        [ j | (j, x) <- zip [i..] ps, Set.member (n - i) x ]

substitute :: Map Natural (Set Natural) -> [Set Natural] -> [Set Natural]
substitute m = map $ foldMap \n -> Map.lookupDefault n Set.empty m

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

------ Benchmarks ------

type Inputs f = [Mono Ord f]

data FoldBench = forall c d f g.
  (Pretty c d f g, [Container, Show1] ** [c, d, f, g]) =>
  FoldBench [Example (FoldIn c d f) g]

testFoldr :: FoldBench -> IO ()
testFoldr (FoldBench xs) = case fromExamples xs of
  Nothing -> putStrLn "Inconsistent examples."
  Just f  -> putStrLn $ prettyRes $ sketchFoldr f

simpleInputs :: Inputs []
simpleInputs =
  [ Mono @Integer []
  , Mono @Integer [1]
  , Mono @Integer [2,3]
  , Mono @Integer [4,5,6]
  ]

simpleBench :: Each [Show1, Prtty, Container] f =>
  (forall a. [a] -> f a) -> FoldBench
simpleBench model = FoldBench @_ @_ @Identity $ simpleInputs <&>
  \(Mono xs) -> Example (Pair (Pair (Const ()) (Const ()))
    (coerce xs)) (model xs)

tailBench, initBench, revBench :: FoldBench
tailBench = simpleBench \case { [] -> []; _:xs -> xs }
initBench = simpleBench \case { [] -> []; xs -> init xs }
revBench  = simpleBench reverse

headBench, lastBench :: FoldBench
headBench = simpleBench \case { [] -> Nothing; x:_  -> Just x }
lastBench = simpleBench \case { [] -> Nothing; xs -> Just (last xs) }

lengthBench :: FoldBench
lengthBench = simpleBench (genericLength @(Const Int _)) 

nullBench :: FoldBench
nullBench = simpleBench $ Const . null

intInputs :: Inputs (Product (Const Int) [])
intInputs = [0, 1, 2] >>= \n -> simpleInputs <&> mapMono (Pair (Const n))

intBench :: (Show1 f, Prtty f, Container f) =>
  (forall a. Int -> [a] -> f a) -> FoldBench
intBench model = FoldBench @_ @_ @Identity $ intInputs <&>
  \(Mono (Pair (Const i) xs)) ->
    Example (Pair (Pair (Const i) (Const i)) (coerce xs)) (model i xs)

dropBench, takeBench :: FoldBench
dropBench = intBench drop
takeBench = intBench take

indexBench :: FoldBench
indexBench = intBench (flip (!?))

splitAtBench :: FoldBench
splitAtBench = intBench $ (uncurry Pair .) . splitAt

argBench' :: (Show1 f, Prtty f, Container f) =>
  (forall a. a -> [a] -> f a) -> FoldBench
argBench' model = FoldBench @_ @_ @Identity $ argInputs <&>
  \(Mono (Pair (Identity x) xs)) ->
    Example (Pair (Pair (Identity x) (Identity x)) (coerce xs)) (model x xs)

snocBench :: FoldBench
snocBench = argBench' snoc

dupInputs :: Inputs (List Dup)
dupInputs =
  [ Mono @Integer (Compose [])
  , Mono @Integer (Compose [Dup (1,2)])
  , Mono @Integer (Compose [Dup (1,2), Dup (3,4)])
  , Mono @Integer (Compose [Dup (1,2), Dup (3,4), Dup (5,6)])
  ]

-- unzipBench :: FoldBench
-- unzipBench = FoldBench $ dupInputs <&> \(Mono xs) ->
--   Example (Pair (Pair (Const ()) (Const ())) xs)
--     (uncurry Pair $ unzip $ coerce xs)

------ Simple ------

-- class Simplify f where
--   type Simple f a :: Type
--   simplify :: f a -> Simple f a

--   type Simple f a = f a
--   default simplify :: Simple f a ~ f a => f a -> Simple f a
--   simplify = id

-- instance Simplify []
-- instance Simplify Maybe

-- instance Simplify Identity where
--   type Simple Identity a = a
--   simplify = runIdentity

-- instance Simplify (Const k) where
--   type Simple (Const k) a = k
--   simplify = getConst

-- instance (Simplify f, Simplify g) => Simplify (Product f g) where
--   type Simple (Product f g) a = (Simple f a, Simple g a)
--   simplify (Pair x y) = (simplify x, simplify y)

-- instance (Simplify f, Simplify g) => Simplify (Sum f g) where
--   type Simple (Sum f g) a = Either (Simple f a) (Simple g a)
--   simplify (InL x) = Left  (simplify x)
--   simplify (InR y) = Right (simplify y)

-- instance (Functor f, Simplify f, Simplify g) => Simplify (Compose f g) where
--   type Simple (Compose f g) a = Simple f (Simple g a)
--   simplify = simplify . fmap simplify . getCompose

-- instance Simplify Dup where
--   type Simple Dup a = (a, a)
--   simplify = unDup

-- ------ Pretty ------

-- class Pretty a where
--   pretty :: a -> String

-- class Pretty1 f where
--   liftPretty :: (a -> String) -> f a -> String

-- instance Pretty1 Dup where
--   liftPretty p (Dup (x, y)) = "(" ++ p x ++ ", " ++ p y ++ ")"

-- instance Pretty1 Identity where
--   liftPretty = (. runIdentity)

-- instance (Pretty1 f, Pretty1 g) => Pretty1 (Product f g) where
--   liftPretty p (Pair x y) =
--     "(" ++ liftPretty p x ++ ", " ++ liftPretty p y ++ ")"

-- instance (Pretty1 f, Pretty1 g) => Pretty1 (Sum f g) where
--   liftPretty p (InL x) = "Left " ++
--     "(" ++ liftPretty p x ++ ", " ++ liftPretty p y ++ ")"


------ Contexts ------

-- type FoldrType =
--   ( Assoc Symbol (Type -> Type)
--   , Type -> Type
--   , Type -> Type
--   )

type FoldrIn  ctx f = Product (Context ctx) (List f)
type FoldrEx  ctx f g = Morph (FoldrIn ctx f) g
type FoldrAlg ctx f g =
  Morph (Product (Context ctx) (Sum (Product f g) (Const ()))) g

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
          (t, substitute (remap (Pair ctx x) (Compose xs) q) p)

type Number = '["n" :-> Const Int]

simpleBench_ :: Container f =>
  (forall a. [a] -> f a) -> Maybe (FoldrAlg '[] Identity f)
simpleBench_ model = foldrSketch =<< fromExamples do
  simpleInputs <&> mapMono \xs -> Pair (Pair Nil (coerce xs)) (model xs)

takeInputs :: Inputs (FoldrIn Number Identity)
takeInputs = [0 :: Int, 1, 2] >>= \n -> simpleInputs <&> mapMono
  (Pair (Cons Name (Const n) Nil) . coerce)

intBench_ :: Container f =>
  (forall a. Int -> [a] -> f a) -> Maybe (FoldrAlg Number Identity f)
intBench_ model = foldrSketch =<< fromExamples do
  takeInputs <&> mapMono \input@(Pair (Cons _ n Nil) xs) ->
    Pair input $ model (coerce n) (coerce xs)

argInputs :: Inputs (Product Identity [])
argInputs =
  [ Mono @Integer $ Pair 0 []
  , Mono @Integer $ Pair 0 [1]
  , Mono @Integer $ Pair 0 [2,3]
  , Mono @Integer $ Pair 0 [4,5,6]
  ]

-- TODO: something goes wrong here, perhaps context is not used corrcetly in
-- foldrSketch, it seems that if ctx contains values, it messes with the list
-- inputs. We get the same problem with normal the old version, so perhaps
-- substitute or remap are incorrect?
argBench :: Container f =>
  (forall a. a -> [a] -> f a) -> Maybe (FoldrAlg '["x" :-> Identity] Identity f)
argBench model = foldrSketch =<< fromExamples do
  argInputs <&> mapMono \(Pair x xs) -> do
    Pair (Pair (Cons Name x Nil) (coerce xs)) $ model (coerce x) xs

snoc :: a -> [a] -> [a]
snoc x xs = xs ++ [x]

printBench ::
  (All Container [Context ctx, f, g], AllVal Prtty ctx, Prtty f, Prtty g)
  => Maybe (FoldrAlg ctx f g) -> IO ()
printBench = \case
  Nothing -> putStrLn "Unsatisfiable."
  Just xs -> do
    putStrLn "Satisfiable."
    putStrLn ""
    putStrLn $ pp xs

pp :: (All Container [Context ctx, f, g], AllVal Prtty ctx, Prtty f, Prtty g)
  => FoldrAlg ctx f g -> String
pp = ("foldr f e\n  where" ++)
  . concatMap
    ( \(ctx, (fs, es)) ->
      -- TODO: use recoverinput on ctx and input combined.
      -- probably best to do before anything else
      ("\n    " ++) $ prtty 0 ctx $
        concatMap ("\n      " ++) $
          ( fs <&> \(Pair x r, (t, q)) -> "f " <> prtty 11 x
              (" " <> prtty 11 r (" = " <> prtty 0 (recoverOutput t q) ""))
          ) ++
          ( es <&> \(_, (t, q)) -> "e = " <> prtty 0 (recoverOutput t q) ""
          )
    )
  . Map.toList
  . fmap
    ( bimap Map.toList Map.toList
    . Map.splitEither
    . Map.mapKeysMonotonic \case { InL x -> Left x; InR y -> Right y }
    )
  . Map.curry
  . Map.mapKeysMonotonic (\(Pair x y) -> (x, y))
  . Map.mapKeysMonotonic recoverInput
