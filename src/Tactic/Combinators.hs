module Tactic.Combinators where

import Control.Effect.Choose

import Base hiding (replicate, repeat, (<|>))
import Language.Problem
import Tactic

anyOf :: (Has (Throw TacticFailure) sig m, Has Choose sig m) => [m a] -> m a
anyOf [] = notApplicable "out of options"
anyOf xs = foldr1 (<|>) xs

everywhere :: (Tactic sig m, Has Choose sig m) => (Name -> m a) -> m a
everywhere tactic = tactic =<< anyOf . map pure =<< asks variables

everywhere2 :: (Tactic sig m, Has Choose sig m) => (Name -> Name -> m a) -> m a
everywhere2 tactic = do
  vars <- asks variables
  x <- anyOf $ map pure vars
  y <- anyOf $ map pure vars
  unless (x < y) $ notApplicable "require separate variables"
  tactic x y

anywhere :: (Tactic sig m, Has (Catch TacticFailure) sig m) =>
  (Name -> m a) -> m a
anywhere tactic = do
  vars <- asks variables
  firstOf $ tactic <$> vars

anywhere2 :: (Tactic sig m, Has (Catch TacticFailure) sig m) =>
  (Name -> Name -> m a) -> m a
anywhere2 tactic = do
  vars <- asks variables
  let pairs = [(x, y) | x <- vars, y <- vars, x < y]
  firstOf $ uncurry tactic <$> pairs

infixl 2 <|

orElse, (<|) :: Has (Catch TacticFailure) sig m => m a -> m a -> m a
orElse t u = catchError @TacticFailure t $ const u
(<|) = orElse

firstOf :: Has (Error TacticFailure) sig m => [m a] -> m a
firstOf = foldr orElse $ notApplicable "empty list of tactics"

allOf :: Tactic sig m => [m Filling] -> m Filling
allOf = foldr andThen none

repeat :: Tactic sig m => m Filling -> m Filling
repeat tactic = tactic >>> repeat tactic

replicate :: Tactic sig m => Nat -> m Filling -> m Filling
replicate 0 _ = none
replicate n tactic = tactic >>> replicate (n - 1) tactic

until :: (Tactic sig m, Has (Catch TacticFailure) sig m) => m Filling -> m Filling -> m Filling
until t u = t <| u >>> until t u
