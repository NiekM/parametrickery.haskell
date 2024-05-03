{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
-- Exploring a deep embedding of the language. The shallow embedding (at
-- different depths) runs into the issue that we cannot easily inspect the
-- types, at least not without introducing various singleton types etc. A deep
-- embedding allows for example easy inspecting of types, including constraints,
-- as well as multiple type variables.

module Test where

import Base
import Language.Type
import Language.Expr
import Language.Container
import Language.Container.Morphism
import Language.Problem
import Refinements

------

class    ToExpr a    where toVal :: a -> Expr h
instance ToExpr Int  where toVal = Lit . MkInt
instance ToExpr Bool where toVal = Lit . MkBool
instance ToExpr ()   where toVal = const Unit

instance ToExpr a => ToExpr [a] where
  toVal = Lst . map toVal

instance (ToExpr a, ToExpr b) => ToExpr (a, b) where
  toVal = uncurry Pair . bimap toVal toVal

instance (ToExpr a, ToExpr b) => ToExpr (Either a b) where
  toVal = either Inl Inr . bimap toVal toVal

------ Examples ------

sg :: Signature
sg = Signature [("a", Eq)] [("x", Free "a"), ("xs", List (Free "a"))]
  (List (Free "a"))

-- TODO: change ex to something that makes sense.
-- TODO: in general, give some better working examples here.
ex :: Example
ex = Example [toVal @Int 3, toVal @[Int] [2, 4]] (toVal @[Int] [2, 2])

-- >>> pretty sg
-- forall a. (Eq a) => {x : a, xs : [a]} -> [a]

-- >>> pretty $ extendExample sg ex
-- a0 [a1, a2] | {a0} /= {a1} /= {a2} -> [{a1}, {a1}]

prb :: Problem
prb = Problem
  { sig = Signature
    { vars = [("a", None)]
    , ctxt = [("x", Free "a"), ("y", Free "a"), ("z", Free "a")]
    , goal = Free "a"
    }
  , exs =
    [ Example [v1, v2, v2] v2
    , Example [v2, v1, v2] v2
    , Example [v2, v2, v1] v2
    ]
  } where
    v1 = toVal @Int 1; v2 = toVal @Int 2

-- >>> pretty prb
-- _ : forall a. {x : a, y : a, z : a} -> a
-- _ 1 2 2 = 2
-- _ 2 1 2 = 2
-- _ 2 2 1 = 2

-- >>> pretty <$> check prb
-- Left PositionConflict

tst :: Problem
tst = Problem
  { sig = Signature { vars = [], ctxt = [], goal = Base Int }
  , exs = [Example [] (toVal @Int 4)]
  }

-- >>> pretty tst
-- _ : Int
-- _ = 4

pairExample :: Problem
pairExample = Problem
  { sig = Signature
    { vars = [("a", None), ("b", None)]
    , ctxt = [("x", Free "a"), ("y", Free "b")]
    , goal = Tup (Free "a") (Free "b")
    }
  , exs =
    [ Example [toVal @Int 1, toVal True ] $ toVal @(Int, Bool) (1,  True)
    , Example [toVal False, toVal @Int 3] $ toVal @(Bool, Int) (False, 3)
    ]
  }

-- >>> pretty pairExample
-- _ : forall a b. {x : a, y : b} -> a * b
-- _ 1 True = 1 , True
-- _ False 3 = False , 3

-- >>> pretty <$> check pairExample
-- Right [a0 b0 -> ({a0}, {b0})]

introPairExample :: [[Problem]]
introPairExample = introPair pairExample

-- >>> pretty introPairExample
-- [ [ _ : forall a b. {x : a, y : b} -> a
--   _ 1 True = 1
--   _ False 3 = False
--   , _ : forall a b. {x : a, y : b} -> b
--   _ 1 True = True
--   _ False 3 = 3 ] ]

sg1 :: Signature
sg1 = Signature [("a", Ord)] [("xs", List (Free "a"))] (List (Free "a"))

ex1 :: Example
ex1 = Example [toVal @[Int] [1,2,4,1,2,3,4,5,1,2]] (toVal @[Int] [1,2,3,4,5])

-- >>> pretty $ extendExample sg1 ex1
-- [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
--  | {a0 = a3 = a8} <= {a1 = a4 = a9} <= {a5} <= {a2 = a6} <= {a7} -> [ {a0
-- , a3
-- , a8}
-- , {a1, a4, a9}
-- , {a5}
-- , {a2, a6}
-- , {a7} ]
