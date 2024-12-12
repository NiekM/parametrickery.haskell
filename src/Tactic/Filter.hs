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
        when (t /= u) $ throwError NotApplicable
        examples <- forM (zip terms problem.examples) \case
          (List inputs, Example scope (List outputs)) -> do
            unless (isFilter inputs outputs) $ throwError NotApplicable
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
      _ -> throwError NotApplicable

-- TODO: filterSome

