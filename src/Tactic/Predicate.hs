module Tactic.Predicate where

import Control.Carrier.Reader

import Base
import Language.Problem

import Tactic

predicate :: Tactic sig m => Text -> m Bool -> m Filling
predicate message p = p >>= \case
  True -> none
  False -> throwError $ NotApplicable message

-- NOTE: this is inefficient, since realizability has to be recomputed
-- -- This is only applicable if the examples are fully covering.
-- covering :: Tactic sig m => m Filling
-- covering = do
--   context <- ask
--   problem <- ask
--   case check context problem of
--     Left err -> throwError $ Unrealizable err
--     Right rules -> case coverage context problem.signature rules of
--       Total -> none
--       _ -> throwError $ NotApplicable "no full coverage"

-- This is only applicable if there are no examples.
someExamples :: Tactic sig m => m Filling
someExamples = predicate "no examples left" do
  problem <- ask @Problem
  return $ not $ null problem.examples

-- This is only applicable if there are no examples.
noExamples :: Tactic sig m => m Filling
noExamples = predicate "some examples left" do
  problem <- ask @Problem
  return $ null problem.examples
