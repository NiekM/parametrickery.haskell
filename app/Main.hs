{-# LANGUAGE BlockArguments #-}

module Main where

import Data.SBV
import Data.SBV.Control
import Control.Monad
import Control.Exception

import Pipeline (FoldInputs)
import Pipeline qualified
import PaperBench

settings :: SMTConfig
settings = defaultSMTCfg
  { solverSetOptions = ReproducibleResourceLimit 10_000_000
  : solverSetOptions defaultSMTCfg
  , timing = PrintTiming
  }

checkOne :: FoldInputs -> IO (Either SomeException Bool)
checkOne = try . isSatisfiableWith settings . Pipeline.foldr

checkAll :: [(String, FoldInputs)] -> IO ()
checkAll xs = forM_ xs \(name, bench) -> do
  let name' = take width $ name ++ ':' : repeat ' '
  s <- checkOne bench
  putStrLn $ name' ++ case s of
    Left  _     -> "Timeout"
    Right False -> "Unsatisfiable"
    Right True  -> "Satisfiable"
  return ()
  where width = 2 + maximum (length . fst <$> xs)

main :: IO ()
main = do
  let runs = 10 :: Int

  putStrLn "------ Shape complete ------"
  replicateM_ runs do checkAll preludeBenches
  putStrLn "------ Shape incomplete ------"
  replicateM_ runs do checkAll incompleteBenches
