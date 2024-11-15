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
import Language.Generics
import Language.Problem
import Language.Parser
import Language.Pretty
import Language.Prelude
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

instance IsString Problem where
  fromString = (.value) . fromString @(Named Problem)

isFold :: Named Problem -> [Either TacticFailure Filling]
isFold problem = runTactic datatypes problem.value $ anywhere fold

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
  let milliseconds = 1_000_000
  bs <- forM bench \problem -> do
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
  let failed = zip bench bs & map ((.name) . fst) . filter (not . snd)
  putStrLn ""
  print $ "Failed:" <+> sep (punctuate ", " $ map pretty failed)
  where
    gen :: Named Problem -> IO (Maybe (Program Void))
    gen problem = case synth problem.value of
      Nothing -> return Nothing
      Just r -> return (Just r)

    testAndPrint :: Named Problem -> Program Void -> IO Bool
    testAndPrint problem result = do
      let f = norm mempty result
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

data Options = Options
  { tactic :: Refinement SynthC
  , fuel :: Maybe Nat
  }

def :: Options
def = Options auto Nothing

data Solution = Solution
  { weight :: Nat
  , extract :: Filling
  , next :: Maybe Solution
  } deriving (Eq, Ord, Show)

instance Pretty Solution where
  pretty solution = prettySplit solution.extract

synthesize :: Options -> Problem -> Maybe Solution
synthesize options problem = makeSolution
  . map (bimap getSum $ norm mempty)
  . whileJust . map sequence
  . runSearch . search datatypes
  . limitFuel options.fuel
  $ runTac problem options.tactic
  where
    limitFuel Nothing = fmap Just
    limitFuel (Just n) = limit n

    whileJust = catMaybes . takeWhile isJust

    makeSolution :: [(Nat, Filling)] -> Maybe Solution
    makeSolution = \case
      [] -> Nothing
      (n, f) : xs -> Just . Solution n f $ makeSolution xs

synth :: Problem -> Maybe (Program Void)
synth problem = do
  solution <- synthesize def problem
  vacant solution.extract

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

prettySplit :: (Pretty h, Pretty (Named h)) => Expr l (Named h) -> Doc ann
prettySplit e
  | null helpers = pretty e
  | otherwise = nest 2 $ vsep
    [ pretty $ fmap (.name) e
    , nest 2 . vsep $ "where"
      : List.intersperse "" helpers
    ]
  where helpers = map pretty $ holes e

tryOut :: Interpret a => Problem -> a
tryOut = interpret . fromJust . synth
