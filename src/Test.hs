{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test where

import GHC.Generics

import Data.Set qualified as Set
import Data.Map qualified as Map
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (fromJust, catMaybes)
import Data.Text.IO qualified as Text
import System.IO.Unsafe qualified as Unsafe
import System.Directory
import System.Timeout

import Control.Monad.Search
import Control.Carrier.Reader
import Control.Carrier.Choose.Church
import Control.Carrier.Error.Either
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
import Language.Generics
import Language.Problem
import Language.Parser
import Language.Pretty
import Language.Prelude
import Language.Relevance
import Utils

import Tactic
import Tactic.Combinators
import Tactic.Filter qualified as Tactic
import Tactic.Fold qualified as Tactic
import Tactic.Map qualified as Tactic
import Tactic.Relation qualified as Tactic
import Synth

import Test.QuickCheck hiding (Success, Failure, total)
import Language.Arbitrary qualified as Arbitrary

import Bench

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

{-# NOINLINE benches #-}
benches :: [Named Problem]
benches = Unsafe.unsafePerformIO do
  xs <- listDirectory "data/bench/"
  forM (reverse xs) \name -> do
    content <- Text.readFile $ "data/bench/" <> name
    return $ parse content

getBench :: Name -> Named Problem
getBench name = Named name . fromJust $ find name benches

instance IsString (Named Problem) where
  fromString = getBench . fromString

instance IsString Problem where
  fromString = (.value) . fromString @(Named Problem)

isAFold :: Problem -> Solution
isAFold = synthesize def
  { solutions = Nothing
  , tactic = everywhere Tactic.fold
  }

type TacticC m = ReaderC Problem
  (ReaderC Settings (ReaderC Context (ErrorC TacticFailure (FreshC m))))

runTactic :: Functor m => Context -> Problem -> TacticC m a ->
  m (Either TacticFailure a)
runTactic ctx problem = evalFresh . runError . runReader ctx
  . runReader defaultSettings . runReader problem

isFold :: Named Problem -> [Either TacticFailure Filling]
isFold problem = runTactic datatypes problem.value $ everywhere Tactic.fold

runBench :: [Named Problem] -> IO ()
runBench benchmark = do
  forM_ benchmark \problem -> do
    putStrLn ""
    print $ "Problem:" <+> pretty problem.name
    putStrLn ""
    forM_ (isFold problem) \case
      Left (NotApplicable _) -> return ()
      Left (PropagationError err) -> print $ pretty err
      Left TraceIncomplete -> putStrLn "Trace incomplete"
      Left (Unrealizable conflict) -> print $ pretty conflict
      Right f -> do
        let f' = withNames "_" f
        print . prettyNamed problem.name $ fmap (.name) f'
        putStrLn "  where"
        forM_ (holes f') \(Named name subproblem) -> case runCheck subproblem of
          Left conflict -> print $ pretty conflict
          Right rules -> do
            print . indent 4 $ statements $
              prettyNamed name subproblem.signature
              : (prettyNamed name <$> rules)
            putStrLn ""

paperBench :: IO ()
paperBench = runBench bench'
  where
    bench' = benches & filter \x -> x.name `elem`
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
fullBench = runBench benches

synthAll :: IO ()
synthAll = do
  let milliseconds = 1_000_000
  bs <- forM benches \problem -> do
    putStrLn ""
    print $ "Problem:" <+> pretty problem.name
    putStrLn ""
    res <- timeout milliseconds $ gen problem
    case res of
      Nothing -> False <$ putStrLn "Synthesis failed: timeout"
      Just Nothing -> False <$ putStrLn "Synthesis failed: exhaustive"
      Just (Just p) -> testAndPrint problem p
  putStrLn ""
  let passed = length $ filter id bs
  let total = length bs
  print $ sep
    [pretty passed, "out of", pretty total, "synthesized"]
  let failed = zip benches bs & map ((.name) . fst) . filter (not . snd)
  putStrLn ""
  print $ "Failed:" <+> sep (punctuate ", " $ map pretty failed)
  where
    gen :: Named Problem -> IO (Maybe (Program Void))
    gen problem = case synth problem.value of
      Nothing -> return Nothing
      Just r -> return (Just r)

    testAndPrint :: Named Problem -> Program Void -> IO Bool
    testAndPrint problem result = do
      let f = normalize result
      print . indent 2 $ prettyNamed problem.name f
      case vacant f of
        Nothing -> False <$ putStrLn "Some holes left!"
        Just p -> do
          putStrLn ""
          xs <- testExtract p problem.value
          let passed = length $ filter id xs
          let total = length xs
          print $ sep
            [pretty passed, "out of", pretty total, "tests passed"]
          return $ and xs

synth :: Problem -> Maybe (Program Void)
synth problem = case synthesize def problem of
  Success ((_, Finished program) :| _) -> Just program
  _ -> Nothing

runCheck :: Problem -> Either Conflict [Rule]
runCheck = runReader datatypes . check

testExtract :: Program Void -> Problem -> IO [Bool]
testExtract program problem = forM problem.examples \example ->
  let
    inputs = map Value example.inputs
    expr = Apps program inputs
  in case normalize expr of
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
--   Yes. A paramorphism is strictly stronger than elim.
-- - How well does relevance analysis reflect ease of synthesis?
-- - Is progress purely based on relevance?
--

-- DONE:
-- - Can we do anamorphisms? It seems not.
--   Because the input of a coalgebra is unconstrained.
--   TODO: but is there some dual to unrealizability for anamorphisms?
--   it seems that some dual notion should exist. although the problem lies in
--   the fact that the coalgebra has an infinite input.
--

tryOut :: Interpret a => Problem -> a
tryOut = interpret . fromJust . synth
