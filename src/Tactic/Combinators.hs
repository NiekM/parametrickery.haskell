module Tactic.Combinators where

import Base
import Language.Problem
import Tactic

anywhere :: (Tactic sig m, Alternative m) => (Name -> m a) -> m a
anywhere tactic = tactic =<< oneOf =<< asks variables

anywhere2 :: (Tactic sig m, Alternative m) => (Name -> Name -> m a) -> m a
anywhere2 tactic = do
  vars <- asks variables
  x <- oneOf vars
  y <- oneOf vars
  guard $ x < y
  tactic x y

anyOne :: (Tactic sig m, Has (Catch TacticFailure) sig m) =>
  (Name -> m a) -> m a
anyOne tactic = do
  vars <- asks variables
  firstOf $ tactic <$> vars

anyTwo :: (Tactic sig m, Has (Catch TacticFailure) sig m) =>
  (Name -> Name -> m a) -> m a
anyTwo tactic = do
  vars <- asks variables
  let pairs = [(x, y) | x <- vars, y <- vars, x < y]
  firstOf $ uncurry tactic <$> pairs

infixl 2 <|

orElse, (<|) :: Has (Catch TacticFailure) sig m => m a -> m a -> m a
orElse t u = catchError @TacticFailure t $ const u
(<|) = orElse

firstOf :: Has (Error TacticFailure) sig m => [m a] -> m a
firstOf = foldr orElse $ throwError NotApplicable

-- TODO: can we have an empty tactic at the end? maybe for that we should remove
-- Named from filling
allOf :: (Has (Catch TacticFailure) sig m, Tactic sig m) =>
  [m Filling] -> m Filling
allOf = foldr1 andThen
