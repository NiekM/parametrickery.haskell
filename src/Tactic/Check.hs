module Tactic.Check (rerealize) where

import Control.Carrier.Error.Either
import Control.Carrier.Reader

import Base
import Language.Container.Morphism
import Language.Problem
import Language.Coverage
import Tactic.Core
import Tactic.Extract

-- Recompute realizability
rerealize :: Tactic sig m => m Filling -> m Filling
rerealize cnt = do
  context <- ask
  problem <- ask
  Settings { realizabilityLevel, checkCoverage } <- ask
  -- NOTE: not performing realizability breaks the map < foldr relation, so requires a weaker tactic.
  case realizabilityLevel of
    NoRealizability -> cnt
    MonoRealizability -> case monoCheck problem of
      Nothing -> cnt
      Just xs -> throwError . Unrealizable $ MonoConflict xs
    PolyRealizability -> case check context problem of
      Left err -> throwError $ Unrealizable err
      Right rules -> if checkCoverage
        then case coverage context problem.signature rules of
          Total -> cnt >>> extract
          _ -> cnt
        -- NOTE: should we make this an option?
        -- Reconstruction seems to improve performance slightly by simplifying the resulting constraint.
        else local (reconstruct rules) cnt
