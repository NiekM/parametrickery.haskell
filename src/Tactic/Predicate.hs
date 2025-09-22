{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Tactic.Predicate where

import Control.Carrier.Reader

import Base
import Language.Problem
import Language.Container.Morphism
import Language.Coverage

import Tactic

predicate :: Tactic sig m => Text -> m Bool -> m Filling
predicate message p = p >>= \case
  True -> none
  False -> notApplicable message

-- This is only applicable if the examples are fully covering.
covering :: Tactic sig m => m Filling
covering = do
  problem <- ask @Problem
  ctx <- ask
  case check ctx problem of
    Left err -> throwError $ Unrealizable err
    Right rules -> case coverage ctx problem.signature rules of
      Total -> none
      _ -> notApplicable "no full coverage"

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
