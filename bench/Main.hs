module Main where

import Base

import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import System.Timeout (timeout)
import Control.Exception (evaluate)
import Test.Tasty.Bench
import Test.QuickCheck hiding (Success, Failure)

import Language.Generics (Interpret(..))
import Language.Parser
import Language.Problem
import Language.Prelude
import Tactic
import Tactic.Fold qualified as Tactic
import Synth

import Test.Compare
import Bench hiding (testSynthesis)
import System.Directory (listDirectory)

benchProblem :: Arguments -> Named Problem -> Benchmark
benchProblem args (Named name problem) =
  bench (show $ pretty name) $ whnf (synthesize args) problem

paperBench :: [Named Model]
paperBench = models & filter \model -> model.name `elem`
  [ "null"
  , "length"
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
    Just (Failure Exhausted) -> return (blue "unrealizable", True)
    Just (Success ((_, Unfinished _filling) :| _)) -> return (yellow "realizable", True)
    Just (Success ((_, Finished program) :| _))
      | testProblem program problem -> do
        result <- quickCheckWithResult stdArgs { chatty = False }
          . withMaxSize 25 $ comparison model (interpret program)
        return if isSuccess result
          then (green "success", True)
          else (red "overfitted", False)
      | otherwise -> return (red_bg "inconsistent result", False)
    where
      red    text = "\ESC[31m" ++ text ++ "\ESC[0m"
      green  text = "\ESC[32m" ++ text ++ "\ESC[0m"
      yellow text = "\ESC[33m" ++ text ++ "\ESC[0m"
      blue   text = "\ESC[34m" ++ text ++ "\ESC[0m"
      red_bg text = "\ESC[41m" ++ text ++ "\ESC[0m"

synthBench :: IO ()
synthBench = do
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

main :: IO ()
main = do
  listBench

listBench :: IO ()
listBench = runBenchmark "data/fold_detection/lists/"

load :: Name -> IO Problem
load name = do
  content <- Text.readFile $ "data/bench/" <> Text.unpack name.getName
  case lexParse (parser @(Named Problem)) content of
    Nothing -> error $ "Failed to parse " <> show (pretty name)
    Just problem -> return problem.value

foldCheck :: Named Problem -> Benchmark
foldCheck (Named name problem) = bench (Text.unpack name.getName) $ whnf (isFold "xs") problem

isFold :: Name -> Problem -> Bool
isFold var problem = case runSingle defaultSettings datatypes problem (Tactic.fold var) of
  Left _ -> False
  Right _ -> True

runBenchmark :: FilePath -> IO ()
runBenchmark dir = do
  files <- listDirectory dir
  bs <- forM files \name -> do
    content <- Text.readFile $ dir <> name
    case lexParse parser content of
      Nothing -> error $ "Failed to parse " <> show (pretty name)
      Just problem -> return problem

  defaultMain $ map foldCheck bs

