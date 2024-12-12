module Tactic.Relation where

import Base

import Language.Expr
import Language.Problem
import Language.Type

import Tactic

-- TODO: these should add some value in scope that tells the totality checker
-- that some cases are not possible anymore.

elimEq :: Tactic sig m => Name -> Name -> m Filling
elimEq name1 name2 = do
  x <- getArg name1
  y <- getArg name2
  problem <- ask @Problem
  case (x, y) of
    (Arg (Free a) xs, Arg (Free b) ys)
      | a == b
      , Eq a `elem` problem.signature.constraints
      -> do
      let bools = Arg (Data "Bool" []) $ Bool <$> zipWith (==) xs ys
      elimArg (Apps (Var "eq") [Var name1, Var name2]) bools
    _ -> throwError NotApplicable

elimOrd :: Tactic sig m => Name -> Name -> m Filling
elimOrd name1 name2 = do
  x <- getArg name1
  y <- getArg name2
  problem <- ask @Problem
  case (x, y) of
    (Arg (Free a) xs, Arg (Free b) ys)
      | a == b
      , Ord a `elem` problem.signature.constraints
      -> do
      let ords = Arg (Data "Ordering" []) $ Ordering <$> zipWith compare xs ys
      elimArg (Apps (Var "cmp") [Var name1, Var name2]) ords
    _ -> throwError NotApplicable

