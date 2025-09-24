module Tactic.Combinators where

import Control.Effect.Choose

import Base hiding (replicate, repeat, (<|>))
import Language.Problem
import Tactic.Core

anyOf :: (Tactic sig m, Has Choose sig m) => [m a] -> m a
anyOf [] = throwError $ NotApplicable "out of options"
anyOf xs = foldr1 (<|>) xs

everywhere :: (Tactic sig m, Has Choose sig m) => (Name -> m a) -> m a
everywhere tactic = tactic =<< anyOf . map pure =<< asks variables

everywhere2 :: (Tactic sig m, Has Choose sig m) => (Name -> Name -> m a) -> m a
everywhere2 tactic = do
  vars <- asks variables
  x <- anyOf $ map pure vars
  y <- anyOf $ map pure vars
  unless (x < y) $ throwError $ NotApplicable "require separate variables"
  tactic x y
