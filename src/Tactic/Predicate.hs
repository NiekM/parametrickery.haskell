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
covering = predicate "no full coverage" do
  problem <- ask @Problem
  rules <- liftThrow Unrealizable (check problem)
  coverage problem.signature rules <&> \case
    Total -> True
    _ -> False

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
