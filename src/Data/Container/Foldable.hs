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
import Control.Monad.Error.Class
import Data.Foldable
import Data.Bifunctor (bimap)
import Data.List (intercalate, (!?), intersperse)
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
import Utils

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

-- A partial container morphism
type Morph f g = Map (Shape f) (Shape g, Origins)

-- Turn an example into its monomorphic form.
toMorph :: (Container f, Container g) => Example f g -> Morph f g
toMorph (Example i o) =
  Map.singleton (shape i) (shape o, origins (positions i) (positions o))

-- TODO: do something with these conflicts.
data Conflict = ShapeConflict | PositionConflict

orErr :: MonadError e m => e -> Maybe a -> m a
orErr e = maybe (throwError e) return

merge :: (MonadError Conflict m, Container f, Container g) =>
  [Morph f g] -> m (Morph f g)
merge = Map.unionsWithA \ys -> do
  let (ss, ps) = NonEmpty.unzip ys
  s <- orErr ShapeConflict    $ allSame ss
  p <- orErr PositionConflict $ consistent ps
  return (s, p)

fromExamples :: (MonadError Conflict m, Container f, Container g) =>
  [Example f g] -> m (Morph f g)
fromExamples = merge . map toMorph

consistent :: NonEmpty Origins -> Maybe Origins
consistent = Multi.consistent . foldl1 Multi.intersection

type List = Compose []

sketchMap :: [Example (List f) (List g)] -> Maybe [Example f g]
sketchMap = fmap concat . traverse
  \(Example (Compose xs) (Compose ys)) -> pairUpWith Example xs ys

------ Pretty variables ------

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

------------------------------

------ Contexts ------

type FoldrIn  ctx f = Product (Context ctx) (List f)
type FoldrEx  ctx f g = Morph (FoldrIn ctx f) g
type FoldrAlg ctx f g =
  Morph (Product (Context ctx) (Sum (Product f g) (Const ()))) g

-- TODO: use some monad with MonadWriter (for missing inputs) and MonadError
-- (for unrealizability)
foldrSketch :: (All Container [Context ctx, f, g], MonadError Conflict m)
  => FoldrEx ctx f g -> m (FoldrAlg ctx f g)
foldrSketch m = Map.toList m & merge . fst . partitionWith
  \(s, (t, p)) -> case s of
    Pair ctx (Compose []) ->
      Left $ Map.singleton (Pair ctx (InR (Const ()))) (t, p)
    Pair ctx (Compose (x:xs)) ->
      case Map.lookup (Pair ctx (Compose xs)) m of
        -- TODO: don't just throw away these results
        Nothing     -> Right . Pair ctx $ Compose xs
        Just (u, q) -> Left $ Map.singleton (Pair ctx (InL (Pair x u)))
          (t, Multi.compose (remap ctx x q) p)
  where
    -- Given the shape of the context, the shape of the first element of the
    -- input list and the origins of the recursive call, compute the remapping
    -- of origins that should be applied to the output.
    remap :: All Container [ctx, f] =>
      Shape ctx -> Shape f -> Origins -> Origins
    remap ctx hd rec_p =
      Multi.inverse $ Multi.union
      (positions (Pair ctx hd) & Multi.fromMap . Map.mapWithKey \k _ -> k)
      (Multi.compose mid_old new_mid)
      where
        len = fromIntegral $ length ctx + length hd
        new_mid = rec_p & Multi.mapKeysMonotonic (+ len)
        elems = Set.unions $ Multi.elems new_mid
        mid_old = Multi.fromMap $ elems & Map.fromSet
          \k -> if k < fromIntegral (length ctx)
            then k
            else k + fromIntegral (length hd)

data FoldrBench = forall ctx f g.
  [Container, Pretty] ** [Context ctx, f, g] => FoldrBench
  { name :: String
  , examples :: [Example (FoldrIn ctx f) g]
  }

data FoldrRes = forall ctx f g.
  [Container, Pretty] ** [Context ctx, f, g] =>
  FoldrRes { alg :: Either Conflict (FoldrAlg ctx f g) }

runBench :: FoldrBench -> IO ()
runBench (FoldrBench name examples) = do
  putStrLn $ "Testing " <> name <> "...\n"
  case examples of
    [] -> putStrLn "No examples."
    -- If there is at least one example, we use its context to retrieve the
    -- names of variables in scope.
    Mono (Pair (Pair ctx _) _) : _ -> do
      let vars = variables ctx
      case fromExamples examples of
        Left _ -> putStrLn "Unsatisfiable. (inconsistent input)"
        Right f -> case foldrSketch f of
          Left _ -> putStrLn $ "Unsatisfiable. (" <> name <> " is not a fold)"
          Right alg -> do
            putStrLn "Satisfiable."
            putStrLn ""
            putStrLn $ pp (name <> concatMap (' ':) vars) alg
  putStrLn ""

-- TODO: return some Doc rather than String to make pretty printing more
-- composable. For example, this would allow indenting all of it at once.
pp :: forall ctx f g. [Container, Pretty] ** [Context ctx, f, g] =>
  String -> FoldrAlg ctx f g -> String
pp lhs = (lhs <> " = foldr f e\n  where" ++)
  . concatMap
    ( \(ctx, (fs, es)) ->
      ("\n    " ++) $ pretty 0 ctx $
        concatMap ("\n      " ++) $
          ( fs <&> \(Pair x r, (t, q)) -> "f " <> pretty 11 x
              (" " <> pretty 11 r (" = " <> pretty 0 (recoverOutput t q) ""))
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

simpleInputs :: Inputs (FoldrIn '[] Identity)
simpleInputs =
  [ Mono @Integer []
  , Mono @Integer [1]
  , Mono @Integer [2,3]
  , Mono @Integer [4,5,6]
  ] <&> mapMono (Pair Nil . coerce)

intInputs :: Inputs (FoldrIn '["n" :-> Const Int] Identity)
intInputs = [0, 1, 2] >>= \n -> simpleInputs <&> mapMono
  \(Pair Nil xs) -> Pair (Cons (Const n) Nil) xs

listInputs :: Inputs (FoldrIn '["xs" :-> []] Identity)
listInputs =
  [ Mono @Integer $ Pair [] []
  , Mono @Integer $ Pair [] [1]
  , Mono @Integer $ Pair [1] []
  , Mono @Integer $ Pair [1] [2]
  , Mono @Integer $ Pair [1] [2,3]
  , Mono @Integer $ Pair [1,2] []
  , Mono @Integer $ Pair [1,2] [3]
  , Mono @Integer $ Pair [1,2] [3,4]
  ] <&> mapMono \(Pair xs ys) -> Pair (Cons xs Nil) (coerce ys)

argInputs :: Inputs (FoldrIn '["x" :-> Identity] Identity)
argInputs =
  [ Mono @Integer $ Pair 0 []
  , Mono @Integer $ Pair 0 [1]
  , Mono @Integer $ Pair 0 [2,3]
  , Mono @Integer $ Pair 0 [4,5,6]
  ] <&> mapMono \(Pair x xs) -> Pair (Cons x Nil) (coerce xs)

dupInputs :: Inputs (FoldrIn '[] Dup)
dupInputs =
  [ Mono @Integer $ Compose []
  , Mono @Integer $ Compose [Dup (1,2)]
  , Mono @Integer $ Compose [Dup (1,2), Dup (3,4)]
  , Mono @Integer $ Compose [Dup (1,2), Dup (3,4), Dup (5,6)]
  ] <&> mapMono (Pair Nil)

nestedInputs :: Inputs (FoldrIn '[] [])
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
  ] <&> mapMono (Pair Nil)

simpleBench :: (Container f, Pretty f) =>
  String -> (forall a. [a] -> f a) -> FoldrBench
simpleBench name model = FoldrBench @_ @Identity name $ simpleInputs <&>
  mapMono \(Pair Nil xs) -> Pair (Pair Nil (coerce xs)) (model $ coerce xs)

indexBench :: (Container f, Pretty f) =>
  String -> (forall a. Int -> [a] -> f a) -> FoldrBench
indexBench name model = FoldrBench @_ @Identity name $
  intInputs <&> mapMono \input@(Pair (Cons n Nil) xs) ->
    Pair input $ model (coerce n) (coerce xs)

argBench :: (Container f, Pretty f) =>
  String -> (forall a. a -> [a] -> f a) -> FoldrBench
argBench name model = FoldrBench @_ @Identity name $
  argInputs <&> mapMono \input@(Pair (Cons x Nil) xs) -> do
    Pair input $ model (coerce x) (coerce xs)

listBench :: (Container f, Pretty f) =>
  String -> (forall a. [a] -> [a] -> f a) -> FoldrBench
listBench name model = FoldrBench @_ @Identity name $
  listInputs <&> mapMono \input@(Pair (Cons xs Nil) ys) ->
    Pair input $ model xs (coerce ys)

nestedBench :: [Container, Pretty] ** [f, g] =>
  String -> Inputs (FoldrIn '[] f) -> (forall a. [f a] -> g a) -> FoldrBench
nestedBench name inputs model = FoldrBench name $
  inputs <&> mapMono \input@(Pair Nil xs) ->
    Pair input (model $ coerce xs)

bench :: [FoldrBench]
bench =
  [ simpleBench "null"        $ Const . null
  , simpleBench "length"      $ Const . length
  , simpleBench "headMay"     headMay
  , simpleBench "lastMay"     lastMay
  , simpleBench "tail"        safeTail
  , simpleBench "init"        safeInit
  , simpleBench "reverse"     reverse
  , indexBench  "index"       $ flip (!?)
  , indexBench  "drop"        drop
  , indexBench  "take"        take
  , indexBench  "splitAt"     $ (uncurry Pair .) . splitAt
  , argBench    "cons"        (:)
  , argBench    "snoc"        snoc
  , argBench    "intersperse" intersperse
  , argBench    "headDef"     headDef
  , argBench    "lastDef"     lastDef
  , listBench   "append"      (++)
  , listBench   "prepend"     $ flip (++)
  , listBench   "zip"         $ ((Compose . fmap Dup) .) . zip
  , nestedBench "unzip"       dupInputs $ Compose . Dup . unzip . fmap unDup
  , nestedBench "concat"      nestedInputs concat
  ] where
    headMay, lastMay :: [a] -> Maybe a
    headMay   = \case { [] -> Nothing; y:_ -> Just y }
    lastMay   = \case { [] -> Nothing; xs  -> Just $ last xs }
    headDef, lastDef :: a -> [a] -> Identity a
    headDef x = Identity . \case { [] -> x; y:_ -> y }
    lastDef x = Identity . \case { [] -> x; xs  -> last xs }
    safeTail, safeInit :: [a] -> [a]
    safeTail  = \case { [] -> []; _:xs -> xs }
    safeInit  = \case { [] -> []; xs -> init xs }
    snoc :: a -> [a] -> [a]
    snoc x xs = xs ++ [x]

------ Utils ------

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
