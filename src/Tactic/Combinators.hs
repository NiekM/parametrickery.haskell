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

infixl 0 <|

orElse, (<|) :: Has (Catch TacticFailure) sig m => m a -> m a -> m a
orElse t u = catchError @TacticFailure t $ const u
(<|) = orElse
