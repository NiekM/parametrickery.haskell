{-# LANGUAGE UndecidableInstances #-}

module Data.Container.Foldable where

-- TODO: separate in many files:
-- 1. One for containers (shapes, positions, morphisms)
-- 2. One for sketching/example propagation
-- 3. One for benchmarks

-- This is all completely separate from the SMT stuff, so maybe make it a
-- different project?

import GHC.TypeLits
import Data.Foldable
import Data.Bifunctor (bimap)
import Data.List
  (intercalate, (!?), intersperse, subsequences, permutations, inits, tails)
import Control.Monad.State
import Data.Map.Utils qualified as Map
import Data.Map.Multi (Multi)
import Data.Map.Multi qualified as Multi
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.List.NonEmpty qualified as NonEmpty

import Base
import Data.Mono
import Data.Dup
import Data.Functor.Signatures
import Pretty
import Utils

type Example f g = Mono Ord (Product f g)

{-# COMPLETE Example #-}
pattern Example :: () => forall a. Ord a => f a -> g a -> Example f g
pattern Example input output = Mono (Pair input output)

data Blank = Blank
  deriving stock (Eq, Ord)

instance Show Blank where show _ = "·"

type Shape f = f Blank

shape :: Functor f => f a -> Shape f
shape = (Blank <$)

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

maybeToEither :: e -> Maybe a -> Either e a
maybeToEither e = maybe (Left e) Right

merge :: (Container f, Container g) =>
  [Morph f g] -> Either Conflict (Morph f g)
merge = Map.unionsWithA \ys -> do
  let (ss, ps) = NonEmpty.unzip ys
  s <- maybeToEither ShapeConflict    $ allSame ss
  p <- maybeToEither PositionConflict $ consistent ps
  return (s, p)

fromExamples :: (Container f, Container g) =>
  [Example f g] -> Either Conflict (Morph f g)
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

type FoldrIn f = Product Ctx (List f)
type FoldrEx f g = Morph (FoldrIn f) g
type FoldrAlg f g =
  Morph (Product Ctx (Sum (Product f g) (Const ()))) g

foldrSketch :: (Container f, Container g) =>
  FoldrEx f g -> FoldrRes f g
foldrSketch m = Map.toList m & uncurry FoldrRes . first merge . partitionWith
  \(s, (t, p)) -> case s of
    Pair ctx (Compose []) ->
      Left $ Map.singleton (Pair ctx (InR (Const ()))) (t, p)
    Pair ctx (Compose (x:xs)) ->
      case Map.lookup (Pair ctx (Compose xs)) m of
        Nothing     -> Right . Pair ctx $ Compose xs
        Just (u, q) -> Left $ Map.singleton (Pair ctx (InL (Pair x u)))
          (t, Multi.compose (remap ctx x q) p)
  where
    -- Given the shape of the context, the shape of the first element of the
    -- input list and the origins of the recursive call, compute the remapping
    -- of origins that should be applied to the output.
    remap :: (Container ctx, Container f) =>
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

-- TODO: this is exactly where we would add options for restricting the context
-- of the arguments to foldr. But how exactly? Quite tricky to describe this.
data FoldrBench = forall f g.
  (Container f, Container g) => FoldrBench
  { name     :: String
  , examples :: [Example (FoldrIn f) g]
  }

data FoldrRes f g = FoldrRes
  { algebra :: Either Conflict (FoldrAlg f g)
  , missing :: [Shape (FoldrIn f)]
  }

runBench :: FoldrBench -> IO ()
runBench (FoldrBench name examples) = do
  putStrLn $ "Testing " <> name <> "...\n"
  case examples of
    [] -> putStrLn "No examples."
    -- If there is at least one example, we use its context to retrieve the
    -- names of variables in scope.
    Mono (Pair (Pair (Ctx ctx) _) _) : _ -> case fromExamples examples of
      Left _ -> putStrLn "Unsatisfiable. (inconsistent input)"
      Right f -> do
        let FoldrRes algebra missing = foldrSketch f
        putStr $ completenessWarning missing
        case algebra of
          Left _ -> putStrLn $ "Unsatisfiable. (" <> name <> " is not a fold)"
          Right alg -> do
            putStrLn "Satisfiable."
            putStrLn ""
            putStrLn $ showFoldr name (Map.keys ctx) alg
  putStrLn ""

-- Returns a warning of shape incompleteness based on a list of missing inputs
-- of recursive calls.
-- TODO: use a less hacky way to print in red.
completenessWarning :: (Container f, Pretty f) =>
  [Shape (FoldrIn f)] -> String
completenessWarning [] = ""
completenessWarning xs = unlines $
  [ ""
  , "\ESC[91m[WARNING]\ESC[0m The example set is not shape complete!"
  , "Examples for the following inputs are missing:"
  , ""
  ] ++
  map (\i -> case recoverInput i of
    Pair (Ctx m) x | Map.null m -> "  " <> pretty 0 x ""
    Pair m x -> "  " <> pretty 0 m (' ' : pretty 0 x ""))
    xs
  ++ [ ""
  , "Satisfiability will be overapproximated in terms of"
  , "the maximal shape complete subset of examples."
  , ""
  ]

-- TODO: return some Doc rather than String to make pretty printing more
-- composable. For example, this would allow indenting all of it at once.
-- This would also allow using some colours ideally.
showFoldr :: (Container f, Container g) =>
  String -> [String] -> FoldrAlg f g -> String
showFoldr name args =
  (name <> concatMap (' ':) args <> " = foldr f e\n  where" ++)
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

simpleInputs :: Inputs (FoldrIn Identity)
simpleInputs =
  [ Mono @Integer []
  , Mono @Integer [1]
  , Mono @Integer [2,3]
  , Mono @Integer [4,5,6]
  ] <&> mapMono (Pair (Ctx mempty) . coerce)

intInputs :: Inputs (FoldrIn Identity)
intInputs = [0 :: Natural, 1, 2] >>= \n -> simpleInputs <&> mapMono
  \(Pair _ xs) -> Pair (Ctx $ Map.singleton "n" (AnyFun (K Nat) (Const n))) xs

listInputs :: Inputs (FoldrIn Identity)
listInputs =
  [ Mono @Integer $ Pair [] []
  , Mono @Integer $ Pair [] [1]
  , Mono @Integer $ Pair [1] []
  , Mono @Integer $ Pair [1] [2]
  , Mono @Integer $ Pair [1] [2,3]
  , Mono @Integer $ Pair [1,2] []
  , Mono @Integer $ Pair [1,2] [3]
  , Mono @Integer $ Pair [1,2] [3,4]
  ] <&> mapMono \(Pair xs ys) ->
    Pair (Ctx $ Map.singleton "xs" (AnyFun (L I) $ coerce xs)) (coerce ys)

argInputs :: Inputs (FoldrIn Identity)
argInputs =
  [ Mono @Integer $ Pair 0 []
  , Mono @Integer $ Pair 0 [1]
  , Mono @Integer $ Pair 0 [2,3]
  , Mono @Integer $ Pair 0 [4,5,6]
  ] <&> mapMono \(Pair x xs) ->
    Pair (Ctx $ Map.singleton "x" $ AnyFun I x) (coerce xs)

dupInputs :: Inputs (FoldrIn Dup)
dupInputs =
  [ Mono @Integer $ Compose []
  , Mono @Integer $ Compose [Dup (1,2)]
  , Mono @Integer $ Compose [Dup (1,2), Dup (3,4)]
  , Mono @Integer $ Compose [Dup (1,2), Dup (3,4), Dup (5,6)]
  ] <&> mapMono (Pair $ Ctx mempty)

nestedInputs :: Inputs (FoldrIn [])
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
  ] <&> mapMono (Pair $ Ctx mempty)

-- TODO: If the inputs are also of type AnyFun, we can match them up in a single
-- function i.o. having all these separate ones.

simpleBench :: (Container f, Pretty f) =>
  String -> (forall a. [a] -> f a) -> FoldrBench
simpleBench name model = FoldrBench name $ simpleInputs <&>
  mapMono \(Pair m xs) -> Pair (Pair m xs) (model $ coerce xs)

indexBench :: forall f. (Container f, Pretty f) =>
  String -> (forall a. Int -> [a] -> f a) -> FoldrBench
indexBench name model = FoldrBench @Identity @f name $
  intInputs <&> mapMono \input@(Pair (Ctx m) xs) -> case Map.lookup "n" m of
    Just (AnyFun (K Nat) n) -> Pair input $ model (fromIntegral n) (coerce xs)
    _ -> error "Incorrect context"

argBench :: forall f. (Container f, Pretty f) =>
  String -> (forall a. a -> [a] -> f a) -> FoldrBench
argBench name model = FoldrBench @Identity @f name $
  argInputs <&> mapMono \input@(Pair (Ctx m) xs) -> case Map.lookup "x" m of
    Just (AnyFun I x) -> Pair input $ model (coerce x) (coerce xs)
    _ -> error "Incorrect context"

listBench :: forall f. (Container f, Pretty f) =>
  String -> (forall a. [a] -> [a] -> f a) -> FoldrBench
listBench name model = FoldrBench @Identity @f name $
  listInputs <&> mapMono \input@(Pair (Ctx m) ys) -> case Map.lookup "xs" m of
    Just (AnyFun (L I) xs) -> Pair input $ model (coerce xs) (coerce ys)
    _ -> error "Incorrect context"

nestedBench :: (Container f, Container g) =>
  String -> Inputs (FoldrIn f) -> (forall a. [f a] -> g a) -> FoldrBench
nestedBench name inputs model = FoldrBench name $
  inputs <&> mapMono \input@(Pair _ xs) ->
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
  , simpleBench "subseqs"     $ Compose . subsequences
  , simpleBench "perms"       $ Compose . permutations
  , simpleBench "inits"       $ Compose . inits
  , simpleBench "tails"       $ Compose . tails
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
  , nestedBench "transpose"   nestedInputs $ Compose . transpose
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

-- TODO: what would `Morph c f g` look like?
-- i.e. how do we extend Partial Morphisms to work for arbitrary constraints c
-- For c a = (a ~ t), it should be a partial function over t
-- For c a = (), it should be a partial container morphism
-- c implies some relation that should hold over the position morphism.

-- type M c f g = Map (Shape f) (Shape g, Origins)
