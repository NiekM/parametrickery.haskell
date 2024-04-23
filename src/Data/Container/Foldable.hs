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
  (intercalate, (!?), intersperse, subsequences, permutations, inits, tails, nub)
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

import Constraint

data Example c f g where
  Example :: forall a c f g. (Ord a, c a) => f a -> g a -> Example c f g

-- type Example f g = Mono Ord (Product f g)

-- {-# COMPLETE Example #-}
-- pattern Example :: () => forall a. Ord a => f a -> g a -> Example f g
-- pattern Example input output = Mono (Pair input output)

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
type Morph c f g = Map (Rel c, Shape f) (Shape g, Origins)

toMorph :: forall c f g. (Container f, Container g, Constr c) =>
  Example c f g -> Morph c f g
toMorph (Example i o) =
  Map.singleton (rel, shape i) (shape o, origins (positions i) (positions o))
  where rel = computeRel (Proxy @c) . Map.fromList . zip [0..] $ toList i

-- TODO: do something with these conflicts.
data Conflict = ShapeConflict | PositionConflict
  deriving (Eq, Ord, Show)

maybeToEither :: e -> Maybe a -> Either e a
maybeToEither e = maybe (Left e) Right

merge :: (Container f, Container g, Constr c) =>
  [Morph c f g] -> Either Conflict (Morph c f g)
merge = Map.unionsWithA \ys -> do
  let (ss, ps) = NonEmpty.unzip ys
  s <- maybeToEither ShapeConflict    $ allSame ss
  p <- maybeToEither PositionConflict $ consistent ps
  return (s, p)

fromExamples :: (Container f, Container g, Constr c) =>
  [Example c f g] -> Either Conflict (Morph c f g)
fromExamples = merge . map toMorph

consistent :: NonEmpty Origins -> Maybe Origins
consistent = Multi.consistent . foldl1 Multi.intersection

type List = Compose []

sketchMap :: [Example c (List f) (List g)] -> Maybe [Example c f g]
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

{-

Perhaps it should print something like:

{x = a}

  foo b [c]
    | ascending [a, b, c] = ... NOTE: this misses equality
    | ascending [b, a, c] = ...

  foo b [c]
    | a < b == c = ...
    | b == a < c = ...


-}

recoverInput :: Traversable f => Shape f -> f Var
recoverInput s = populate s [Var 0 ..]

recoverOutput :: Traversable f => Shape f -> Origins -> f Vars
recoverOutput t q = populate t $ map (Vars . Set.mapMonotonic Var)
  (Multi.elems q)

------------------------------

------ Contexts ------

type FoldrIn f = Product Ctx (List f)
type FoldrEx c f g = Morph c (FoldrIn f) g
type FoldrAlg c f g =
  Morph c (Product Ctx (Sum (Product f g) (Const ()))) g

elim :: (Container f, Constr c) => Rel c -> Shape (List f)
  -> a -> (Shape f -> Rel c -> Shape (List f) -> a) -> a
elim r xs nil cons = case xs of
  Compose [] -> nil
  Compose (y:ys) -> cons y (updateRel m r) (Compose ys)
    where
      l = fromIntegral $ length xs
      k = fromIntegral $ length y
      m = Map.fromList $ [0 .. l - 1] <&> \n -> (n,)
        if n < k then Nothing else Just $ n - k

-- TODO: how do we do sketching with foldr for ad-hoc polymorphic functions?
foldrSketch :: (Container f, Container g, Constr c) =>
  FoldrEx c f g -> FoldrRes c f g
foldrSketch m = Map.toList m & uncurry FoldrRes . first merge . partitionWith
  \((r, Pair ctx s), (t, p)) -> elim r s
    (Left $
      Map.singleton (updateRel mempty r, Pair ctx (InR (Const ()))) (t, p))
    \x r' xs -> case Map.lookup (r', Pair ctx xs) m of
      Nothing     -> Right (r', Pair ctx xs)
      Just (u, q) -> Left $ Map.singleton (r, Pair ctx (InL (Pair x u)))
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
data FoldrBench = forall f g c.
  (Container f, Container g, Constr c) => FoldrBench
  { name     :: String
  , examples :: [Example c (FoldrIn f) g]
  }

data FoldrRes c f g = FoldrRes
  { algebra :: Either Conflict (FoldrAlg c f g)
  , missing :: [(Rel c, Shape (FoldrIn f))]
  }

runBench :: FoldrBench -> IO ()
runBench (FoldrBench name examples) = do
  putStrLn $ "Testing " <> name <> "...\n"
  case examples of
    [] -> putStrLn "No examples."
    -- If there is at least one example, we use its context to retrieve the
    -- names of variables in scope.
    Example (Pair (Ctx ctx) _) _ : _ -> case fromExamples examples of
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
-- TODO: take ad-hoc polymorphism into account.
completenessWarning :: (Constr c, Container f, Pretty f) =>
  [(Rel c, Shape (FoldrIn f))] -> String
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
    (map snd xs)
  ++ [ ""
  , "Satisfiability will be overapproximated in terms of"
  , "the maximal shape complete subset of examples."
  , ""
  ]

-- TODO: return some Doc rather than String to make pretty printing more
-- composable. For example, this would allow indenting all of it at once.
-- This would also allow using some colours ideally.
showFoldr :: (Container f, Container g) =>
  String -> [String] -> FoldrAlg c f g -> String
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
  . Map.mapKeysMonotonic \(x, y) -> case recoverInput y of Pair a b -> (a, b)
  -- . Map.mapKeysMonotonic \case { Pair x y -> (x, y) }
  -- -- TODO: actually use constraints when recovering inputs
  -- . Map.mapKeysMonotonic (recoverInput . snd)

------ Benchmarks ------

type Inputs f = [Mono Ord f]

simpleInputs :: Inputs (FoldrIn Identity)
simpleInputs =
  [ Mono @Integer []
  , Mono @Integer [1]
  , Mono @Integer [2,3]
  , Mono @Integer [4,5,6]
  ] <&> mapMono (Pair (Ctx mempty) . coerce)

eqInputs :: Inputs (FoldrIn Identity)
eqInputs =
  [ Mono @Integer []
  , Mono @Integer [1]
  , Mono @Integer [1,2]
  , Mono @Integer [2,2]
  , Mono @Integer [4,5,6]
  , Mono @Integer [4,4,5]
  , Mono @Integer [4,5,4]
  ] <&> mapMono (Pair (Ctx mempty) . coerce)

ordInputs :: Inputs (FoldrIn Identity)
ordInputs =
  [ Mono @Integer []
  , Mono @Integer [1]
  , Mono @Integer [1,1]
  , Mono @Integer [1,2]
  , Mono @Integer [2,1]
  , Mono @Integer [4,4,5]
  , Mono @Integer [4,5,4]
  , Mono @Integer [4,5,6]
  , Mono @Integer [6,5,4]
  ] <&> mapMono (Pair (Ctx mempty) . coerce)

-- NOTE: I ignored duplicates in the input.
-- Note that this has the additional precondition that the second argument is a
-- sorted list, so this should be represented in the list.
insertInputs :: Inputs (FoldrIn Identity)
insertInputs =
  [ Mono @Integer $ Pair 0 []
  , Mono @Integer $ Pair 0 [1]
  , Mono @Integer $ Pair 1 [0]
  , Mono @Integer $ Pair 0 [1,3]
  , Mono @Integer $ Pair 2 [1,3]
  , Mono @Integer $ Pair 4 [1,3]
  , Mono @Integer $ Pair 0 [1,3,5]
  , Mono @Integer $ Pair 2 [1,3,5]
  , Mono @Integer $ Pair 4 [1,3,5]
  , Mono @Integer $ Pair 6 [1,3,5]
  ] <&> mapMono \(Pair x xs) ->
    Pair (Ctx $ Map.singleton "x" $ AnyFun I x) (coerce xs)

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

eqBench :: (Container f, Pretty f) =>
  String -> (forall a. Eq a => [a] -> f a) -> FoldrBench
eqBench name model = FoldrBench @Identity @_ @Eq name $ eqInputs <&>
  \(Mono (Pair m xs)) -> Example (Pair m xs) (model $ coerce xs)

ordBench :: (Container f, Pretty f) =>
  String -> (forall a. Ord a => [a] -> f a) -> FoldrBench
ordBench name model = FoldrBench @Identity @_ @Ord name $ ordInputs <&>
  \(Mono (Pair m xs)) -> Example (Pair m xs) (model $ coerce xs)

insertBench :: forall f. (Container f, Pretty f) =>
  String -> (forall a. Ord a => a -> [a] -> f a) -> FoldrBench
insertBench name model = FoldrBench @Identity @f @Ord name $
  insertInputs <&> \(Mono input@(Pair (Ctx m) xs)) -> case Map.lookup "x" m of
    Just (AnyFun I x) -> Example input $ model (coerce x) (coerce xs)
    _ -> error "Incorrect context"

simpleBench :: (Container f, Pretty f) =>
  String -> (forall a. [a] -> f a) -> FoldrBench
simpleBench name model = FoldrBench @_ @_ @Trivial name $ simpleInputs <&>
  \(Mono (Pair m xs)) -> Example (Pair m xs) (model $ coerce xs)

indexBench :: forall f. (Container f, Pretty f) =>
  String -> (forall a. Int -> [a] -> f a) -> FoldrBench
indexBench name model = FoldrBench @Identity @f @Trivial name $
  intInputs <&> \(Mono input@(Pair (Ctx m) xs)) -> case Map.lookup "n" m of
    Just (AnyFun (K Nat) n) ->
      Example input $ model (fromIntegral n) (coerce xs)
    _ -> error "Incorrect context"

argBench :: forall f. (Container f, Pretty f) =>
  String -> (forall a. a -> [a] -> f a) -> FoldrBench
argBench name model = FoldrBench @Identity @f @Trivial name $
  argInputs <&> \(Mono input@(Pair (Ctx m) xs)) -> case Map.lookup "x" m of
    Just (AnyFun I x) -> Example input $ model (coerce x) (coerce xs)
    _ -> error "Incorrect context"

listBench :: forall f. (Container f, Pretty f) =>
  String -> (forall a. [a] -> [a] -> f a) -> FoldrBench
listBench name model = FoldrBench @Identity @f @Trivial name $
  listInputs <&> \(Mono input@(Pair (Ctx m) ys)) -> case Map.lookup "xs" m of
    Just (AnyFun (L I) xs) -> Example input $ model (coerce xs) (coerce ys)
    _ -> error "Incorrect context"

nestedBench :: (Container f, Container g) =>
  String -> Inputs (FoldrIn f) -> (forall a. [f a] -> g a) -> FoldrBench
nestedBench name inputs model = FoldrBench @_ @_ @Trivial name $
  inputs <&> \(Mono input@(Pair _ xs)) ->
    Example input (model $ coerce xs)

bench :: [FoldrBench]
bench =
  [ eqBench     "nub"         nub
  , ordBench    "sort"        $ foldr insert []
  , insertBench "insert"      insert
  , simpleBench "null"        $ Const . null
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
    insert :: Ord a => a -> [a] -> [a]
    insert x [] = [x]
    insert x (y:ys)
      | x < y = x:y:ys
      | otherwise = y : insert x ys

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

------ Ad-hoc polymorphism! ------

data ConSig c where
  NoC  :: ConSig Trivial
  EqC  :: ConSig Eq
  OrdC :: ConSig Ord

-- TODO: does it make sense to make relations dependent on the shape of the
-- input? A binary relation can be represented by a nested input functor, e.g.
-- if the input is a list, the relational component for Eq is a [[Bool]]. In a
-- way, this is already the representation we use! But then with the container
-- representation of the functors, where nesting corresponds to having a pair of
-- positions as the input. It is a bit strange however how we mix and match with
-- using the container vs algebraic representations.
data Rel (c :: Type -> Constraint) :: Type where
  NoR  :: Rel Trivial
  EqR  :: Map (Natural, Natural) Bool     -> Rel Eq
  OrdR :: Map (Natural, Natural) Ordering -> Rel Ord

deriving instance Eq   (Rel c)
deriving instance Ord  (Rel c)
deriving instance Show (Rel c)

class Constr (c :: Type -> Constraint) where
  computeRel :: c a => Proxy c -> Map Natural a -> Rel c
  updateRel :: Map Natural (Maybe Natural) -> Rel c -> Rel c

instance Constr Trivial where
  computeRel _ _ = NoR
  updateRel _ = id

instance Constr Eq where
  computeRel _ = EqR . compute2 (==)
  updateRel f (EqR x) = EqR $ update2 f x

instance Constr Ord where
  computeRel _ = OrdR . compute2 compare
  updateRel f (OrdR x) = OrdR $ update2 f x

-- data Nested (n :: Natural) k a where
--   Single :: a -> Nested 0 k a
--   Nested :: Map k (Nested n k a) -> Nested (1 + n) k a

-- deriving instance (Show k, Show a) => Show (Nested n k a)

-- instance Eq a => Eq (Nested 0 k a) where
--   Single x == Single y = x == y
--   _ == _ = False

-- delete :: Ord k => k -> Nested n k a -> Nested n k a
-- delete x = \case
--   Single c -> Single c
--   Nested m -> Nested . fmap (delete x) . Map.delete x $ m

-- nest :: Ord k => (k -> Nested n k a) -> [k] -> Nested (1 + n) k a
-- nest f xs = Nested $ Map.fromList $ xs <&> \x -> (x, f x)

-- make1 :: Ord k => (k -> a) -> [k] -> Nested 1 k a
-- make1 f = nest $ Single . f

-- make2 :: Ord k => (k -> k -> a) -> [k] -> Nested 2 k a
-- make2 f xs = xs & nest \x -> make1 (f x) xs

compute2 :: Ord k => (a -> a -> b) -> Map k a -> Map (k, k) b
compute2 f m = Map.uncurry $ m <&> \x -> m <&> \y -> f x y

update2 :: Ord k => Map k (Maybe k) -> Map (k, k) a -> Map (k, k) a
update2 f = Map.mapKeysMaybe \(n, m) -> do
  n' <- join $ Map.lookup n f
  m' <- join $ Map.lookup m f
  return (n', m')
-- lower :: Natural -> Nested n Natural a -> Nested n Natural a
-- lower n = \case
--   Single c -> Single c
--   Nested m -> Nested . fmap (lower n) . Map.mapKeysMaybe
--     (\k -> if k < n then Nothing else Just (k - n)) $ m
