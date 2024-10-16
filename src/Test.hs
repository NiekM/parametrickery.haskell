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
import System.Timeout

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
getBench name = fromJust $ find name bench

-- TODO: rewrite this so that we get errors again.
isFold :: Named Problem -> Maybe ProofState
isFold = fmap snd . tryTactics [anywhere fold]

runBench :: [Named Problem] -> IO ()
runBench benchmark = do
  forM_ benchmark \problem -> do
    putStrLn ""
    print $ "Problem:" <+> pretty problem.name
    putStrLn ""
    case isFold problem of
      Just st | [f, e, _] <- st.goals -> do
        print $ pretty problem.name <+>
          "= fold" <+> pretty f.name <+> pretty e.name
        putStrLn "  where"
        print . indent 4 $ pretty f
        putStrLn ""
        print . indent 4 $ pretty e
        putStrLn ""
      _ -> putStrLn "Not a fold."

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
    timeout 1_000_000 case synth problem of
      Nothing -> putStrLn "Synthesis failed"
      Just (_n, r) -> do
        let (f, gs) = extrs r
        print . indent 2 $ pretty f
        forM_ gs $ print . indent 4 . pretty

synth :: Named Problem -> Maybe (Sum Nat, [Named Extract])
synth p = runSearchBest . fmap (.extract) . search $ goal p >> auto 10

tryTactics :: [TacticC SearchC (Program (Named Problem))]
  -> Named Problem -> Maybe (Sum Nat, ProofState)
tryTactics ts problem = runSearchBest . search $ goal problem >> tactics ts

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
