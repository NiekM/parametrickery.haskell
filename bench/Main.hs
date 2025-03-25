module Main where

import Base

import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import System.Timeout (timeout)
import Control.Exception (evaluate)
import Test.Tasty.Bench
import Test.QuickCheck hiding (Success, Failure)

import Language.Generics (Interpret(..))
import Language.Problem
import Tactic
import Synth

import Test.Compare
import Bench hiding (testSynthesis)

benchProblem :: Arguments -> Named Problem -> Benchmark
benchProblem args (Named name problem) =
  bench (show $ pretty name) $ whnf (synthesize args) problem

paperBench :: [Named Model]
paperBench = models & filter \model -> model.name `elem`
  [ "null"
  , "length" -- Does not work because it uses Int
  , "head"
  , "last"
  , "tail"
  , "init"
  , "reverse"
  , "index"
  , "drop"
  , "take"
  , "splitAt"
  , "append"
  , "zip"
  , "unzip"
  , "concat"
  ]

testSynthesis :: Arguments -> Problem -> Model -> IO (String, Bool)
testSynthesis args problem (Model model) = do
  timed <- timeout 1_000_000 . evaluate $ synthesize args problem
  case timed of
    Nothing -> return ("timeout", False)
    Just (Failure Depleted) -> return ("out of fuel", False)
    Just (Failure Exhausted) -> return ("unrealizable", True)
    Just (Success ((_, Unfinished _filling) :| _)) -> return ("realizable", True)
    Just (Success ((_, Finished program) :| _))
      | testProblem program problem -> do
        result <- quickCheckWithResult stdArgs { chatty = False }
          . withMaxSize 25 $ comparison model (interpret program)
        return if isSuccess result
          then ("success", True)
          else ("overfitted", False)
      | otherwise -> return ("inconsistent result", False)

main :: IO ()
main = do

  let args = def { settings = defaultSettings { removeIrrelevant = False } }
  let testBench = models

  problems <- forM testBench \model -> do
    problem <- loadProblem model.name
    return $ fmap (problem,) model

  let maxLength = maximum $ problems <&> Text.length . (.name.getName)

  successful <- problems & filterM \(Named name (problem, model)) -> do
    let len = Text.length name.getName
    (str, res) <- testSynthesis args problem model
    let padding = replicate (maxLength + 3 - len) ' '
    putStrLn $ show (pretty name) <> ":" <> padding <> str
    return res

  let benches = map (fst <$>) successful

  defaultMain $ map (benchProblem args) benches

