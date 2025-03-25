module Tactic.Filter where

import Base
import Control.Effect.Fresh.Named
import Data.List qualified as List

import Language.Expr
import Language.Problem
import Language.Type

import Tactic

isFilter :: Eq a => [a] -> [a] -> Bool
isFilter xs ys = List.filter (`elem` ys) xs == ys

filter :: Tactic sig m => Name -> m Filling
filter name = do
  Arg mono terms <- getArg name
  local (hide [name]) do
    problem <- ask @Problem
    case (mono, problem.signature.output) of
      (Data "List" [t], Data "List" [u]) -> do
        when (t /= u) $ notApplicable "list types do not match"
        examples <- forM (zip terms problem.examples) \case
          (List inputs, Example scope (List outputs)) -> do
            unless (isFilter inputs outputs) $ throwError $ PropagationError "not a filter"
            return $ List.nub inputs <&> \x ->
              Example (scope ++ [x]) $ Bool $ x `elem` outputs
          _ -> error "Not actually lists."
        x <- freshName "x"
        let
          Signature constraints context _ = problem.signature
          signature =
            Signature constraints (context ++ [Named x t]) (Data "Bool" [])
          subproblem = Problem signature $ concat examples
        local (const subproblem) do
          f <- hole True
          let result = Apps (Var "filter") [Lams [x] f, Var name]
          return result
      _ -> notApplicable "filter only works on lists"

-- TODO: filterSome

-- NOTE: one way to generalize filter.
-- It would be cool to define filter in terms of partition, but we'd need to first introduce a 'fst' tactic, which has a wildcard on the second field of a tuple.
partition :: Tactic sig m => Name -> m Filling
partition name = do
  Arg mono terms <- getArg name
  local (hide [name]) do
    problem <- ask @Problem
    case (mono, problem.signature.output) of
      (Data "List" [t], Product [Data "List" [u], Data "List" [v]]) -> do
        when (t /= u || t /= v) $ notApplicable "list types do not match"
        examples <- forM (zip terms problem.examples) \case
          (List inputs, Example scope (Tuple [List trues, List falses])) -> do
            unless (isFilter inputs trues && isFilter inputs falses) $ throwError $ PropagationError "not a partition"
            return $ List.nub inputs <&> \x ->
              Example (scope ++ [x]) $ Bool $ x `elem` trues
          _ -> error "Not actually lists."
        x <- freshName "x"
        let
          Signature constraints context _ = problem.signature
          signature =
            Signature constraints (context ++ [Named x t]) (Data "Bool" [])
          subproblem = Problem signature $ concat examples
        local (const subproblem) do
          f <- hole True
          let result = Apps (Var "partition") [Lams [x] f, Var name]
          return result
      _ -> notApplicable "span only works on `List a -> (List a, List a)`"

