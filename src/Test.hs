{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test where

import Control.Monad.State
import Data.Coerce (coerce)
import Data.Either (isRight, fromRight)
import Data.Bifunctor (bimap)
import Data.Foldable (asum)
import Data.Set qualified as Set
import Data.Map qualified as Map
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Monoid (Alt(..), Sum(..))
import Data.Maybe (fromJust)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Prettyprinter
import System.IO.Unsafe qualified as Unsafe
import System.Directory

import Control.Monad.Search
import Data.PQueue.Max (MaxQueue)
import Data.PQueue.Max qualified as Queue

import Control.Carrier.Reader

import Base
import Data.Map.Multi qualified as Multi
import Data.Named
import Language.Type
import Language.Expr
import Language.Container
import Language.Container.Morphism
import Language.Container.Relation
import Language.Coverage
import Language.Problem
import Language.Parser
import Language.Pretty
import Language.Relevance
import Utils

import Tactic

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
  "_ : (Ord a, Eq b) => {xs : List (a, b)} -> (List a, List b)\n\
  \_ [(1, 2), (3, 4)] = ([1, 3], [2, 4])\n\
  \_ [(1, 2)] = ([1], [2])\n\
  \_ [(1, 2), (1, 2), (1, 2)] = ([1], [2])"

incr :: Problem
incr = parse
  "_ : {xs : List Int} -> List Int\n\
  \_ [1,2,3] = [2,3,4]\n\
  \_ [4,5] = [5,6]\n\
  \_ [6] = [7]"

rel :: Problem
rel = parse
  "_ : {x : a, y : a, z : a} -> List a\n\
  \_ 1 2 1 = [1,2]"

-- TODO: rewrite this so that we get errors again.
isFold :: Problem -> [[Named Spec]]
isFold p = execTactic (anywhere cata p) <&> ((.goals) . snd)

runBench :: [Named Problem] -> IO ()
runBench benchmark = do
  forM_ benchmark \(Named name problem) -> do
    putStrLn ""
    print $ "Problem:" <+> pretty name
    putStrLn ""
    -- TODO: report when it is not applicable (i.e. no list in scope)
    forM_ (isFold problem) \case
      [f, e] -> do
        print $ pretty name <+> "= fold" <+> pretty f.name <+> pretty e.name
        putStrLn "  where"
        print . indent 4 $ pretty f
        putStrLn ""
        print . indent 4 $ pretty e
        putStrLn ""
      _ -> error "Wrong number of subproblems."

paperBench :: IO ()
paperBench = runBench bench'
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

fullBench :: IO ()
fullBench = runBench bench

synth :: Named Problem -> Maybe (Sum Nat, [Extract])
synth p = runSearchBest . fmap fst . search $ subgoal p.name p.value >> auto 50

fillHole :: Expr l Text -> Named (Expr l Text) -> Expr l Text
fillHole expr (Named name filling) = expr >>= \hole ->
  if name == hole then filling else Hole $ MkHole hole

combineFuns :: [Named (Program Text)] -> Named (Program Text)
combineFuns = List.foldl1' \x y -> fmap (`fillHole` y) x

isHole :: Expr l h -> Maybe h
isHole (Hole (MkHole h)) = Just h
isHole _ = Nothing

fromRules :: Named [Rule] -> Maybe (Named (Program Text))
fromRules = mapM \case
  [rule]
    | null rule.input.relations
    , Just ps <- mapM isHole rule.input.shapes
    -> do
    let f p = fromJust . Set.lookupMin $ Multi.lookup p rule.origins
    let fromPos p = Text.pack $ show $ pretty p
    let y = fromTerm rule.output >>= Var . fromPos . f
    return $ lams (fromPos <$> ps) y
  _ -> Nothing

extrs :: [Extract] -> (Named (Program Text), [Named [Rule]])
extrs xs = (norm mempty <$> combineFuns (as ++ cs), ds)
  where
    (as, bs) = xs & mapEither \case
      Fun p -> Left p
      Rules name rs -> Right $ Named name rs
    (cs, ds) = bs & mapEither \r -> maybe (Right r) Left $ fromRules r

runCheck :: Problem -> Either Conflict [Rule]
runCheck = runReader datatypes . check

-- TODO:
-- - Are paramorphisms + relevance superior to catamorphisms?
-- - Can we show that any function is a paramorphism? Or the opposite?
-- - How well does relevance analysis reflect ease of synthesis?
-- - Is progress purely based on relevance?
--

-- DONE:
-- - Can we do anamorphisms? It seems not.
--