{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Prelude hiding (unzip)
import Data.Functor ((<&>), unzip)
import Data.List (transpose)
import Data.List.NonEmpty (NonEmpty(..))
import Data.IORef
import Data.SBV
import Data.SBV.Control
import Data.Time.Clock
import Data.Time.Format
import Control.Monad
import Control.Exception

import Data.List.NonEmpty.Utils
import Sketch.Foldr (FoldExamples)
import Sketch.Foldr qualified as Sketch
import Benchmark

checkAll :: [FoldExamples] -> IO [Maybe (Bool, NominalDiffTime)]
checkAll xs = do
  time <- newIORef 0

  let
    settings :: SMTConfig
    settings = defaultSMTCfg
      { solverSetOptions = ReproducibleResourceLimit 10_000_000
      : solverSetOptions defaultSMTCfg
      , timing = SaveTiming time
      }

    checkOne :: FoldExamples -> IO (Either SomeException Bool)
    checkOne = try . isSatisfiableWith settings . Sketch.foldr

  forM xs $ checkOne >=> \case
    Left  _ -> return Nothing
    Right b -> do
      t <- readIORef time
      return $ Just (b, t)

-- | Merge the results from different runs of the same benchmark, ensuring that
-- they all have the same resulting and computing the average runtime.
merge :: [Maybe (Bool, NominalDiffTime)] -> Maybe (Bool, NominalDiffTime)
merge xs = sequence xs <&> \case
  [] -> error "No values to merge"
  y:ys -> do
    let (bs, ts) = unzip (y :| ys)
    case allSame bs of
      Nothing -> error "Inconsistent realizability result"
      Just b -> (b, average ts)

-- | Print 'NominalDiffTime' in milliseconds.
milliseconds :: NominalDiffTime -> String
milliseconds = formatTime defaultTimeLocale "%_4s" . (*1000)

runBenchmark :: Int -> Benchmark -> IO ()
runBenchmark runs benches = do
  let (names, examples) = unzip benches
  let width = 4 + maximum (map length names)
  results <- replicateM runs do checkAll examples
  forM_ (zip names . map merge $ transpose results) \(name, result) -> do
    putStr . take width $ name ++ repeat ' '
    putStrLn case result of
      Nothing     -> "timeout"
      Just (b, t) -> (if b then "satisfiable  " else "unsatisfiable")
        ++ "  " ++ milliseconds t ++ " ms"

main :: IO ()
main = do
  let runs = 10 :: Int

  -- HACK: this ensures that the SMT solver is 'primed', so that the runtime of
  -- the first benchmark is not inflated by the solver having to initialize.
  -- Additionally ensures that the number of runs is positive.
  True <- isSatisfiable (fromIntegral @_ @(SBV Integer) runs .> 0)

  putStrLn "-------- Shape complete ----------"
  runBenchmark runs Benchmark.shapeComplete

  putStrLn "-------- Shape incomplete --------"
  runBenchmark runs Benchmark.shapeIncomplete
