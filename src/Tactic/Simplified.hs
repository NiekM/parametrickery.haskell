module Tactic.Simplified where

import Base hiding (fail)
import Language.Expr
import Language.Problem

type Spec = Problem
type Sketch = Program

type Tactic = Spec -> [Sketch Spec]

(||) :: Tactic -> Tactic -> Tactic
t || u = \p -> t p ++ u p

(<|) :: Tactic -> Tactic -> Tactic
t <| u = \p -> case t p of
  [] -> u p
  xs -> xs

(>>) :: Tactic -> Tactic -> Tactic
t >> u = \p -> t p >>= \e -> fmap join . sequence . fmap u $ e

succeed :: Tactic
succeed = \p -> [Hole p]

fail :: Tactic
fail = \_ -> []

everywhere :: (Name -> Tactic) -> Tactic
everywhere f = \p -> variables p >>= flip f p

predicate :: (Spec -> Bool) -> Tactic
predicate p = \s -> if p s then [Hole s] else []
