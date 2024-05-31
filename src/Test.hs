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

triple :: Problem
triple = Problem
  { signature = Signature
    { vars = [("a", None)]
    , ctxt = [("x", Free "a"), ("y", Free "a"), ("z", Free "a")]
    , goal = Free "a"
    }
  , examples =
    [ Example [v1, v2, v2] v2
    , Example [v2, v1, v2] v2
    , Example [v2, v2, v1] v2
    ]
  } where
    v1 = toVal @Int 1; v2 = toVal @Int 2

-- >>> pretty triple
-- _ : forall a. {x : a, y : a, z : a} -> a
-- _ 1 2 2 = 2
-- _ 2 1 2 = 2
-- _ 2 2 1 = 2

-- >>> pretty <$> check triple
-- Left PositionConflict

constant :: Problem
constant = Problem
  { signature = Signature { vars = [], ctxt = [], goal = Base Int }
  , examples = [Example [] (toVal @Int 4)]
  }

-- >>> pretty constant
-- _ : Int
-- _ = 4

pairExample :: Problem
pairExample = Problem
  { signature = Signature
    { vars = [("a", None), ("b", None)]
    , ctxt = [("x", Free "a"), ("y", Free "b")]
    , goal = Tup (Free "a") (Free "b")
    }
  , examples =
    [ Example [toVal @Int 1, toVal True ] $ toVal @(Int, Bool) (1,  True)
    , Example [toVal False, toVal @Int 3] $ toVal @(Bool, Int) (False, 3)
    ]
  }

-- >>> pretty pairExample
-- _ : forall a b. {x : a, y : b} -> a * b
-- _ 1 True = 1 , True
-- _ False 3 = False , 3

-- >>> pretty <$> check pairExample
-- Right _ : forall a b. {x : a, y : b} -> a * b
-- _ a0 b0 = ({a0}, {b0})

introPairExample :: [[Problem]]
introPairExample = introPair pairExample

-- >>> pretty introPairExample
-- [ [ _ : forall a b. {x : a, y : b} -> a
--   _ 1 True = 1
--   _ False 3 = False
--   , _ : forall a b. {x : a, y : b} -> b
--   _ 1 True = True
--   _ False 3 = 3 ] ]

zipExample :: Problem
zipExample = Problem
  { signature = Signature
    { vars = [("a", None), ("b", None)]
    , ctxt = [("xs", List (Free "a")), ("ys", List (Free "b"))]
    , goal = List (Tup (Free "a") (Free "b"))
    }
  , examples =
    [ Example [toVal @[Int] [], toVal @[Int] []] (toVal @[(Int, Int)] [])
    , Example [toVal @[Int] [1], toVal @[Int] [2]] (toVal @[(Int, Int)] [(1,2)])
    , Example [toVal @[Int] [1,2], toVal @[Int] [3,4,5]]
      (toVal @[(Int, Int)] [(1,3),(2,4)])
    , Example [toVal @[Int] [1,2,3], toVal @[Int] [4,5]]
      (toVal @[(Int, Int)] [(1,4),(2,5)])
    ]
  }

lenExample :: Problem
lenExample = Problem
  { signature = Signature
    { vars = [("a", None)]
    , ctxt = [("xs", List (Free "a"))]
    , goal = Base Int
    }
  , examples =
    [ Example [toVal @[Int] []] (toVal @Int 0)
    , Example [toVal @[Int] [3]] (toVal @Int 1)
    , Example [toVal @[Int] [2,3]] (toVal @Int 2)
    , Example [toVal @[Int] [1,2,3]] (toVal @Int 3)
    ]
  }

sortExample :: Problem
sortExample = Problem
  { signature = Signature
    { vars = [("a", Ord)]
    , ctxt = [("xs", List (Free "a"))]
    , goal = List (Free "a")
    }
  , examples =
    [ Example [toVal @[Int] []] (toVal @[Int] [])
    , Example [toVal @[Int] [3]] (toVal @[Int] [3])
    , Example [toVal @[Int] [3,2]] (toVal @[Int] [2,3])
    , Example [toVal @[Int] [2,3,1]] (toVal @[Int] [1,2,3])
    ]
    -- [ ([], [])
    -- , ([3], [3])
    -- , ([3,2], [2,3])
    -- , ([2,3,1], [1,2,3])
    -- ] <&> \(i, o) -> Example [toVal @[Int] i] (toVal @[Int] o)
  }

twoRelations :: Problem
twoRelations = Problem
  { signature = Signature
    { vars = [("a", Ord), ("b", Eq)]
    , ctxt = [("xs", List (Tup (Free "a") (Free "b")))]
    , goal = Tup (List (Free "a")) (List (Free "b"))
    }
  , examples =
    [ Example [toVal @[(Int, Int)] [(1,2),(3,4)]] (toVal @([Int], [Int]) ([1,3], [2,4]))
    , Example [toVal @[(Int, Int)] [(1,2)]] (toVal @([Int], [Int]) ([1], [2]))
    , Example [toVal @[(Int, Int)] [(1,2),(1,2),(1,2)]] (toVal @([Int], [Int]) ([1], [2]))
    ]
  }
