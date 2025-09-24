module Tactic.Elim where

import Data.Map qualified as Map

import Control.Carrier.Reader

import Base
import Language.Expr
import Language.Problem
import Language.Type
import Tactic.Core
import Tactic.Hole

elimArg :: Tactic sig m => Program Void -> Arg -> m Filling
elimArg expr arg = do
  ctx <- ask @DataContext
  problem <- ask @Problem
  case split ctx arg problem of
    Left e -> throwError $ NotApplicable $ "elim: " <> e
    Right m -> do
      -- require all cases to have at least some examples
      -- TODO: this tactic should not be disallowed when examples are missing, but during synthesis we should have an option to disallow it.
      -- maybe as an argument to this function? This also disallows e.g. elimOrd when not all cases are present.
      -- TODO: this also breaks fold detection sometimes.
      -- when (any (null . (.examples) . snd) m) $ notApplicable "not all cases have examples"
      arms <- forM m \(a, p) -> local (const p) $ binds [Named "x" a] hole
      return $ App (Elim $ Map.assocs arms) (vacuous expr)

elim :: Tactic sig m => Name -> m Filling
elim name = do
  arg <- getArg name
  local (hide [name]) $ elimArg (Var name) arg

