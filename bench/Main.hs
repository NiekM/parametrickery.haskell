module Main where

import Control.Lens
import Control.Monad
import Data.Void

import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import System.Directory
import System.Timeout (timeout)
import Control.Exception (evaluate)
import Criterion.Main

import Data.Name
import Language.Expr
import Language.Problem
import Language.Parser
import Synth
import Prettyprinter

testExtract :: Program Void -> Problem -> Bool
testExtract program problem = and $ problem.examples <&> \example ->
  let
    inputs = map Value example.inputs
    expr = Apps program inputs
  in case norm mempty expr of
    Value output | output == example.output -> True
    _ -> False

benchProblem :: Named Problem -> Benchmark
benchProblem (Named name problem) =
  bench (show $ pretty name) $ whnf (synthesize def) problem 

main :: IO ()
main = do
  files <- reverse <$> listDirectory "data/bench/"
  problems :: [Named Problem] <- forM files \name -> do
    content <- Text.readFile $ "data/bench/" <> name
    case lexParse parser content of
      Nothing -> error $ "Failed to parse " <> name
      Just problem -> return problem

  let maxLength = maximum $ problems <&> Text.length . (.name.getName)

  results <- problems & filterM \(Named name problem) -> do
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
      Just (Success _ (PartialExtract _filling)) ->
        putStrLn "out of tactics" >> return False
      Just (Success _ (TotalExtract program))
        | testExtract program problem -> putStrLn "success" >> return True
        | otherwise -> putStrLn "inconsistent result" >> return False

  -- TODO: quickCheck against model solutions.
  -- How do we do this properly? Which package is responsible for hosting the
  -- model solutions? How do we pair them up with the problems?

  defaultMain $ map benchProblem results