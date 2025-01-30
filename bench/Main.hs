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
import Language.Parser
import Tactic
import Tactic.Combinators (anywhere)
import Tactic.Fold qualified as Tactic
import Synth

import Test.Compare
import Model qualified

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

loadProblem :: Name -> IO Problem
loadProblem name = do
  content <- Text.readFile $ "data/bench/" <> Text.unpack name.getName
  case lexParse (parser @(Named Problem)) content of
    Nothing -> error $ "Failed to parse " <> show (pretty name)
    Just problem -> return problem.value

data Model = forall a. (Compare a, Interpret a) => Model a

models :: [Named Model]
models =
  [ Named "allSame"           . Model $ Model.allSame @Int
  , Named "append"            . Model $ Model.append @Int
  , Named "breadthFirst"      . Model $ Model.breadthFirst @Int @Int
  -- NOTE: it seems that the innermost fold is not trace complete, and perhaps
  -- cannot be trace complete by providing just toplevel examples.
  , Named "cartesian"         . Model $ Model.cartesian @Int
  , Named "clamp"             . Model $ Model.clamp @Int
  , Named "compress"          . Model $ Model.compress @Int
  , Named "concat"            . Model $ Model.concat @Int
  , Named "cons"              . Model $ Model.cons @Int
  , Named "copyFirst"         . Model $ Model.copyFirst @Int
  , Named "copyLast"          . Model $ Model.copyLast @Int
  -- NOTE: it is all about phrasing! If we say that our tool cannot synthesize
  -- deleteMax, that's not very impressive, but if we show that our tool
  -- exhaustively searched the program space, that sounds much more impressive.
  -- Same for `ordNub`, `splitAt`, etc.
  , Named "deleteMax"         . Model $ Model.deleteMax @Int
  , Named "depth"             . Model $ Model.depth @Int @Int
  , Named "drop"              . Model $ Model.drop @Int
  , Named "dupli"             . Model $ Model.dupli @Int
  , Named "head"              . Model $ Model.head @Int
  , Named "index"             . Model $ Model.index @Int
  , Named "init"              . Model $ Model.init @Int
  , Named "inorder"           . Model $ Model.inorder @Int @Int
  , Named "insert"            . Model $ Model.insert @Int
  , Named "last"              . Model $ Model.last @Int
  , Named "length"            . Model $ Model.length @Int
  , Named "levels"            . Model $ Model.levels @Int @Int
  , Named "maximum"           . Model $ Model.maximum @Int
  , Named "member"            . Model $ Model.member @Int
  , Named "mostCommon"        . Model $ Model.mostCommon @Int
  , Named "nub"               . Model $ Model.nub @Int
  , Named "null"              . Model $ Model.null @Int
  , Named "ordNub"            . Model $ Model.ordNub @Int
  , Named "partitionEithers"  . Model $ Model.partitionEithers @Int @Int
  , Named "pivot"             . Model $ Model.pivot @Int
  , Named "preorder"          . Model $ Model.preorder @Int @Int
  , Named "replicate"         . Model $ Model.replicate @Int
  , Named "reverse"           . Model $ Model.reverse @Int
  , Named "shiftl"            . Model $ Model.shiftl @Int
  , Named "shiftr"            . Model $ Model.shiftr @Int
  , Named "size"              . Model $ Model.size @Int @Int
  , Named "snoc"              . Model $ Model.snoc @Int
  , Named "sort"              . Model $ Model.sort @Int
  , Named "sorted"            . Model $ Model.sorted @Int
  , Named "splitAt"           . Model $ Model.splitAt @Int
  , Named "swap"              . Model $ Model.swap @Int @Int
  , Named "tail"              . Model $ Model.tail @Int
  , Named "take"              . Model $ Model.take @Int
  , Named "unzip"             . Model $ Model.unzip @Int @Int
  , Named "zip"               . Model $ Model.zip @Int @Int
  ]
