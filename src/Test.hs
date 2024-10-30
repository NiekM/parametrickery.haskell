{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test where

import Data.Set qualified as Set
import Data.Map qualified as Map
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (fromJust)
import Data.Text.IO qualified as Text
import System.IO.Unsafe qualified as Unsafe
import System.Directory
import System.Timeout

import Control.Monad.Search
import Control.Carrier.Reader
import Control.Carrier.NonDet.Church
import Control.Effect.Fresh.Named
import Data.String
import Prettyprinter

import Base
import Control.Effect.Search
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
import Tactic.Combinators
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

getBench :: Name -> Named Problem
getBench name = Named name . fromJust $ find name bench

instance IsString (Named Problem) where
  fromString = getBench . fromString

isFold :: Named Problem -> [Either TacticFailure Filling]
isFold problem = runTactic problem.value $ anywhere fold

runBench :: [Named Problem] -> IO ()
runBench benchmark = do
  forM_ benchmark \problem -> do
    putStrLn ""
    print $ "Problem:" <+> pretty problem.name
    putStrLn ""
    forM_ (isFold problem) \case
      Left NotApplicable -> return ()
      Left TraceIncomplete -> putStrLn "Trace incomplete"
      Left (Unrealizable conflict) -> print $ pretty conflict
      Right f -> do
        print . prettyNamed problem.name $ fmap (.name) f
        putStrLn "  where"
        forM_ (holes f) \(Named name subproblem) -> case runCheck subproblem of
          Left conflict -> print $ pretty conflict
          Right rules -> do
            print . indent 4 $ statements $
              prettyNamed name subproblem.signature
              : (prettyNamed name <$> rules)
            putStrLn ""

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
    res <- timeout 1_000_000 $ synthesize problem
    case res of
      Nothing -> putStrLn "Synthesis failed: timeout"
      _ -> return ()
  where
    synthesize :: Named Problem -> IO ()
    synthesize problem = case synth problem of
      Nothing -> putStrLn "Synthesis failed: exhaustive"
      Just (_n, r) -> do
        let f = norm mempty <$> combineFuns r.extracts
        print . indent 2 $ pretty f
        case vacant f.value of
          Nothing -> putStrLn "Some holes left!"
          Just p -> do
            putStrLn ""
            xs <- testExtract p problem.value
            let passed = length $ filter id xs
            let total = length xs
            print $ sep
              [pretty passed, "out of", pretty total, "tests passed"]

synthUpTo :: Nat -> Named Problem -> [(Sum Nat, ProofState)]
synthUpTo fuel problem = map (fmap fromJust) . takeWhile (isJust . snd)
  . runSearch . search . limit fuel $ intro problem >> tactics auto

-- TODO: check that the result has no unsolved holes.
synth :: Named Problem -> Maybe (Sum Nat, ProofState)
synth problem = runSearchBest . search $ intro problem >> staged

tacticsUpTo :: [Refinement SynthC] -> Nat -> Named Problem ->
  [(Sum Nat, ProofState)]
tacticsUpTo ts fuel problem = map (fmap fromJust) . takeWhile (isJust . snd)
  . runSearch . search . limit fuel $ intro problem >> tactics ts

upTo :: Nat -> Named Problem -> [(Sum Nat, ProofState)]
upTo fuel problem = map (fmap fromJust) . takeWhile (isJust . snd)
  . runSearch . search . limit fuel $ intro problem >> staged

tryTactics :: [Refinement SynthC]
  -> Named Problem -> Maybe (Sum Nat, ProofState)
tryTactics ts problem = runSearchBest . search $ intro problem >> tactics ts

runCheck :: Problem -> Either Conflict [Rule]
runCheck = runReader datatypes . check

testExtract :: Program Void -> Problem -> IO [Bool]
testExtract program problem = forM problem.examples \example ->
  let
    inputs = map Value example.inputs
    expr = Apps program inputs
  in case norm mempty expr of
    Value output
      | output == example.output -> return True
      | otherwise -> do
        putStrLn "Test failed"
        print $ "Expected:" <+> pretty example.output
        print $ "Got:" <+> pretty output
        return False
    e -> do
      print $ "Not a value:" <+> pretty e
      return False

-- TODO:
-- - Are paramorphisms + relevance superior to catamorphisms?
-- - Can we show that any function is a paramorphism? Or the opposite?
-- - How well does relevance analysis reflect ease of synthesis?
-- - Is progress purely based on relevance?
--

-- DONE:
-- - Can we do anamorphisms? It seems not.
--
