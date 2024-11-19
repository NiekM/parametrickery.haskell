module Main where

import Base

import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import System.Timeout (timeout)
import Control.Exception (evaluate)
import Criterion.Main
import Test.QuickCheck hiding (Success, Failure)

import Language.Generics (Interpret(..))
import Language.Problem
import Language.Parser
import Synth

import Test.Compare
import Model qualified

benchProblem :: Named Problem -> Benchmark
benchProblem (Named name problem) =
  bench (show $ pretty name) $ whnf (synthesize def) problem 

main :: IO ()
main = do
  problems <- forM models \model -> do
    problem <- loadProblem model.name
    return $ fmap (problem,) model

  let maxLength = maximum $ problems <&> Text.length . (.name.getName)

  successful <- problems & filterM \(Named name (problem, Model model)) -> do
    let len = Text.length name.getName
    let padding = pretty $ replicate (maxLength + 3 - len) ' '
    putStr . show $ pretty name <> ":" <> padding
    timed <- timeout 1_000_000 . evaluate $ synthesize def problem
    case timed of
      Nothing ->
        putStrLn "timeout" >> return False
      Just (Failure Depleted) ->
        putStrLn "out of fuel" >> return False
      Just (Failure Exhausted) ->
        putStrLn "unrealizable" >> return True
      Just (Success _ (Unfinished _filling)) ->
        putStrLn "out of tactics" >> return False
      Just (Success _ (Finished program))
        | testProblem program problem -> do
          let args = stdArgs { chatty = False }
          result <- quickCheckWithResult args . withMaxSize 25 $
            comparison model (interpret program)
          if isSuccess result
            then putStrLn "success" >> return True
            else putStrLn "overfitted" >> return False
        | otherwise -> putStrLn "inconsistent result" >> return False

  let benches = map (fst <$>) successful

  defaultMain $ map benchProblem benches

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
