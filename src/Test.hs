{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test where

import Control.Applicative (Alternative)
import Control.Monad.State
import Data.Coerce (coerce)
import Data.Either (isRight, fromRight)
import Data.Bifunctor (bimap)
import Data.Foldable (asum)
import Data.Map qualified as Map
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Monoid (Alt(..))
import Data.Maybe (fromJust)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Prettyprinter
import System.IO.Unsafe qualified as Unsafe
import System.Directory

import Base
import Data.Map.Multi qualified as Multi
import Data.Named
import Language.Type
import Language.Expr
import Language.Container
import Language.Container.Morphism
import Language.Container.Relation
import Language.Coverage
import Language.Declaration
import Language.Parser
import Refinements
import Utils

import Refinery.Tactic
import Refinery.Tactic.Internal
import Control.Monad.Identity
import Control.Monad.Reader

type Err = String

fresh :: Enum s => MonadState s m => m s
fresh = do
  s <- get
  put (succ s)
  return s

-- TODO: consider using Text i.o. () for holes
instance MonadExtract Text (Expr Text) Err Int Identity where
  hole = do
    s <- fresh
    let h = "a" <> Text.pack (show s)
    pure (h, Hole (MkHole h))
  unsolvableHole _ = hole

-- I really like the way refinery builds up an extract and collects proof goals.
-- However, there's only a single proof extract. Can we build up a tree of
-- possible proof extracts?

type T' a = TacticT Problem (Expr Text) String Int (Reader [Datatype]) a

run :: Problem -> T' () -> [Expr Text]
run p t = runReader (evalTacticT t p 0) datatypes

testTactic :: Problem -> T' () -> IO ()
testTactic p t = case runReader (runTacticT t p 0) datatypes of
  Left _ -> putStrLn "Error"
  Right xs -> forM_ xs \proof -> do
    print $ pretty proof.pf_extract
    forM_ proof.pf_unsolvedGoals \(h, subproblem) ->
      print $ pretty (Named h subproblem)

tuple :: T' ()
tuple = rule \prob -> Tuple <$> mapM subgoal (projections prob)

argRule :: Nat ->
  ((Named Arg, Problem) -> RuleT Problem (Expr Text) String Int (Reader [Datatype]) (Expr Text)) -> T' ()
argRule i f = rule \p -> case pickArg i p of
  Nothing -> unsolvable "argument index"
  Just x -> f x

caseSplit :: [Datatype] -> Named Arg -> Problem -> Map Text (Named Arg, Problem)
caseSplit defs (Named name (Data d ts, terms)) prob = List.foldl' f e xs
  where
    xs = zip terms prob.bindings
    cs = getConstructors d ts defs

    e = Map.fromList $ cs <&> \c ->
      ( c.name
      , ( Named (name <> "_" <> c.name) (c.field, [])
        , Declaration prob.signature []
        )
      )

    f m (Ctr c x, ex) = Map.adjust (bimap
      (\(Named v (ty, ys)) -> Named v (ty, x:ys))
      (\(Declaration sig exs) -> Declaration sig (ex:exs))) c m
    f _ _ = error "Not a constructor"

caseSplit _ _ _ = error "Not a datatype"

unTuple :: Expr h -> [Expr h]
unTuple (Tuple es) = es
unTuple e = [e]

unProduct :: Arg -> [Arg]
unProduct (Product ts, es) = zip ts . List.transpose $ map unTuple es
unProduct a = [a]

split :: Nat -> T' ()
split n = argRule n \(arg, prob) -> do
  defs <- lift ask
  let m = caseSplit defs arg prob
  xs <- forM (Map.elems m) \(Named v a, p) -> do
    as <- forM (unProduct a) \x -> do
      i <- fresh
      return $ Named (v <> Text.pack (show i)) x
    subgoal $ addArgs as p
  return . Ctr "case" $ Tuple xs

splitList :: Arg -> Problem -> [(Text, Arg, Problem)]
splitList (Data "List" [t], terms) problem =
  [ ("Nil", (Top, nilArg)
    , Declaration problem.signature nilExs
    )
  , ("Cons", (Product [t, Data "List" [t]], consArg)
    , Declaration problem.signature consExs
    )
  ]
  where
    (nilArg, nilExs) = unzip nil
    (consArg, consExs) = unzip cons
    nil, cons :: [(Term, Example)]
    (nil, cons) = zip terms problem.bindings & mapEither \case
      (Nil, example) -> Left (Unit, example)
      (Cons y ys, example) -> Right (Tuple [y, ys], example)
      _ -> error "Expected a list"
splitList _ _ = error "Not a list"

fold :: Nat -> T' ()
fold n = argRule n \case
  (Named name (Data "List" [t], terms), problem) -> do
    let
      paired = zip terms problem.bindings
      p = Declaration
        { signature = problem.signature
          { context = Named name (Data "List" [t]) : problem.signature.context }
        , bindings = paired <&> \(i, Example is o) -> Example (i:is) o
        }
    defs <- lift ask
    let
      polyProblem = fromRight (error "") $ check defs p
      recurse = applyProblem polyProblem
      -- We compute the constraints for the nil and the cons case.
      (nil, cons) = paired & mapEither \case
        (Nil, ex) -> Left ex
        (Cons y ys, Example ins out) ->
          case recurse (ys:ins) of
            Nothing -> error "Not shape complete!"
            Just r -> return $ Example (ins ++ [y, r]) out
        _ -> error "Expected a list!"

    -- TODO: we can probably simplify here further by not just adjusting the
    -- examples, but rather generating new Args and then simply giving the
    -- Args a name and inserting them.

    Ctr "fold" . Tuple <$> sequence
      [ subgoal $ problem { bindings = nil }
      , subgoal $ Declaration problem.signature
        { context = problem.signature.context ++
          [ Named (name <> "_h") t
          , Named (name <> "_r") problem.signature.goal
          ]
        } cons
      ]
  (Named name (Data "Tree" [t, u], terms), problem) -> do
    let
      paired = zip terms problem.bindings
      p = Declaration
        { signature = problem.signature
          { context = Named name (Data "Tree" [t, u]) : problem.signature.context }
        , bindings = paired <&> \(i, Example is o) -> Example (i:is) o
        }
    defs <- lift ask
    case check defs p of
      Left _l -> error ""
      Right polyProblem ->
        let
          recurse = applyProblem polyProblem
          -- We compute the constraints for the nil and the cons case.
          (leaf, node) = paired & mapEither \case
            (Ctr "Leaf" x, Example ins out) -> Left $ Example (ins ++ [x]) out
            (Ctr "Node" (Tuple [l, x, r]), Example ins out) ->
              case (recurse (l:ins), recurse (r:ins)) of
                (Just left, Just right) -> return $
                  Example (ins ++ [left, x, right]) out
                _ -> error "Not shape complete!"
            _ -> error "Expected a tree!"
        in Ctr "fold" . Tuple <$> sequence
          [ subgoal $ Declaration problem.signature
            { context = problem.signature.context ++ [Named (name <> "_y") u]
            } leaf
          , subgoal $ Declaration problem.signature
            { context = problem.signature.context ++
              [ Named (name <> "_l") problem.signature.goal
              , Named (name <> "_x") t
              , Named (name <> "_r") problem.signature.goal
              ]
            } node
          ]
  _ -> unsolvable "todo"

-- ToExpr is no longer really necessary now that we have parsing, but it's still
-- useful sometimes.
class    ToExpr a    where toVal :: a -> Expr h
instance ToExpr Int  where toVal = Lit . MkInt
instance ToExpr Bool where toVal = flip Ctr Unit . Text.pack . show
instance ToExpr ()   where toVal = const $ Tuple []

instance ToExpr a => ToExpr [a] where
  toVal = mkList . map toVal

instance (ToExpr a, ToExpr b) => ToExpr (a, b) where
  toVal (x, y) = Tuple [toVal x, toVal y]

------ Utilities ------

parse :: Parse a => Text -> a
parse = fromJust . lexParse parser

inspect :: (Show a, Pretty a) => a -> IO ()
inspect x = do
  print x
  putStrLn ""
  print (pretty x)

instance (Pretty e, Pretty a) => Pretty (Either e a) where
  pretty = either pretty pretty

------ Examples -------

{-# NOINLINE bench #-}
bench :: [Named Problem]
bench = Unsafe.unsafePerformIO do
  xs <- listDirectory "data/bench/"
  forM (reverse xs) \name -> do
    content <- Text.readFile $ "data/bench/" <> name
    return $ parse content

getBench :: Text -> Problem
getBench name = maybe (error "unknown benchmark") (.value) $
  bench & List.find \problem -> problem.name == name

-- triple :: Problem
-- triple = loadProblem "triple"

-- >>> pretty <$> check triple
-- PositionConflict

-- constant :: Problem
-- constant = loadProblem "constant"

-- pairExample :: Problem
-- pairExample = loadProblem "pair"

-- >>> pretty $ check pairExample
-- _ : {x : a, y : b} -> (a, b)
-- _ a0 b0 = (a0, b0)

-- introPairExample :: DisCon Problem
-- introPairExample = introTuple pairExample

-- >>> pretty introPairExample
-- [ [ _ : forall a b. {x : a, y : b} -> a
--   _ 1 True = 1
--   _ False 3 = False
--   , _ : forall a b. {x : a, y : b} -> b
--   _ 1 True = True
--   _ False 3 = 3 ] ]

revExample :: Problem
revExample = getBench "reverse"

zipExample :: Problem
zipExample = getBench "zip"

lenExample :: Problem
lenExample = getBench "length"

tailExample :: Problem
tailExample = getBench "tail"

nubExample :: Problem
nubExample = getBench "nub"

sortExample :: Problem
sortExample = getBench "sort"

-- TODO: can we figure out that in the recursive call, the left list is only
-- relevant for the left output and the right list only relevant for the right
-- output?
pivot :: Problem
pivot = getBench "pivot"

swapExample :: Problem
swapExample = getBench "swap"

append :: Problem
append = getBench "append"

twoRelations :: Problem
twoRelations = parse
  "_ : forall a b. (Ord a, Eq b) => {xs : [(a, b)]} -> ([a], [b])\n\
  \_ [(1, 2), (3, 4)] = ([1, 3], [2, 4])\n\
  \_ [(1, 2)] = ([1], [2])\n\
  \_ [(1, 2), (1, 2), (1, 2)] = ([1], [2])"

isFold :: Problem -> [Either Conflict [PolyProblem]]
isFold p = traverse (check datatypes) <$> xs
  where DisCon xs = introFold p

paperBench :: IO ()
paperBench = do
  forM_ bench' \(Named name problem) -> do
    putStrLn ""
    print $ "Problem:" <+> pretty name
    putStrLn ""
    forM_ (isFold problem) \case
      Left e -> print $ pretty e
      Right [e, f] -> do
        print $ pretty name <+> "= fold f e"
        putStrLn "  where"
        print . indent 4 $ prettyNamed "e" e
        putStrLn ""
        print . indent 4 $ prettyNamed "f" f
        putStrLn ""
      _ -> error "Wrong number of subproblems."
  where
    bench' = bench & filter \x -> x.name `elem`
      [ "null"
      , "length"
      , "head"
      , "last"
      , "tail"
      , "init"
      , "reverse"
      , "drop"
      , "take"
      , "splitAt"
      , "append"
      , "prepend"
      , "zip"
      , "unzip"
      , "concat"
      ]

runBench :: IO ()
runBench = do
  forM_ bench \(Named name problem) -> do
    putStrLn ""
    print $ "Problem:" <+> pretty name
    putStrLn ""
    -- TODO: report when it is not applicable (i.e. no list in scope)
    forM_ (isFold problem) \case
      Left e -> print $ pretty e
      Right [e, f] -> do
        print $ pretty name <+> "= fold f e"
        putStrLn "  where"
        print . indent 4 $ prettyNamed "e" e
        print . indent 4 . parens . pretty $ coverage datatypes e
        putStrLn ""
        print . indent 4 $ prettyNamed "f" f
        print . indent 4 . parens . pretty $ coverage datatypes f
        putStrLn ""
      _ -> error "Wrong number of subproblems."
