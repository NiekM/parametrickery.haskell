{-# LANGUAGE BlockArguments #-}

module Main where

import Data.SBV
import Data.SBV.Control
import Control.Monad

import Bench (FoldBench, checkFoldBench)
import PaperBench

settings :: SMTConfig
settings = defaultSMTCfg
  { solverSetOptions = ReproducibleResourceLimit 10_000_000
  : solverSetOptions defaultSMTCfg
  , timing = PrintTiming
  }

checkAll :: [(String, FoldBench)] -> IO ()
checkAll xs = forM_ xs \(name, bench) -> do
  let name' = take width $ name ++ ':' : repeat ' '
  s <- isSatisfiableWith settings (checkFoldBench bench)
  putStrLn $ name' ++ if s then "Satisfiable" else "Unsatisfiable"
  where width = 2 + maximum (map (length . fst) xs)

main :: IO ()
main = do
  putStrLn "------ Shape complete ------"
  replicateM_ 10 do checkAll preludeBenches
  putStrLn "------ Shape incomplete ------"
  -- We remove unzip because it times out
  replicateM_ 10 do checkAll (filter ((/= "unzip") . fst) incompleteBenches)
