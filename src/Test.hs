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
import Synth

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

getBench :: Name -> Problem
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
isFold p = runSearch f <&> \(_, s) -> s.goals
  where f = search $ goal (Named "p" p) >> anywhere (\a -> applyTactic "p0" . cata a) p

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

synthAll :: IO ()
synthAll = do
  forM_ bench \problem -> do
    putStrLn ""
    print $ "Problem:" <+> pretty problem.name
    putStrLn ""
    -- TODO: report when it is not applicable (i.e. no list in scope)
    case synth problem of
      Nothing -> putStrLn "Synthesis failed"
      Just (_n, r) -> do
        let (f, gs) = extrs r
        print . indent 2 $ pretty f
        forM_ gs $ print . indent 4 . pretty

synth :: Named Problem -> Maybe (Sum Nat, [Named Extract])
synth p = runSearchBest . fmap (.extract) . search $ goal p >> auto 50

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