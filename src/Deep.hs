{-# LANGUAGE OverloadedStrings #-}
-- Exploring a deep embedding of the language. The shallow embedding (at
-- different depths) runs into the issue that we cannot easily inspect the
-- types, at least not without introducing various singleton types etc. A deep
-- embedding allows for example easy inspecting of types, including constraints,
-- as well as multiple type variables.

module Deep where

import Data.Map.Strict qualified as Map
-- import Data.Map.Multi (Multi)
import Data.Map.Multi qualified as Multi
import Data.Map.Utils qualified as Map
import Data.List.NonEmpty qualified as NonEmpty

import Prettyprinter.Utils

import Base
import Language.Type
import Language.Expr
import Language.Container
import Utils

data Problem = Problem
  { sig :: Signature
  , exs :: [Example]
  } deriving stock (Eq, Ord, Show)

-- This is simply a compact representation of a set of input-output examples for
-- a container morphism.
type Morph =
  Map (Map Text Relation, [Expr Position]) (Expr Position, Map Text Origins)

combine :: [MorphExample] -> Either Conflict [MorphExample]
combine = fmap (map fromMorph . Map.assocs) . merge . map toMorph
  where
    toMorph (MorphExample r s t o) = Map.singleton (r, s) (t, o)
    fromMorph ((r, s), (t, o)) = MorphExample r s t o

    merge :: [Morph] -> Either Conflict Morph
    merge = Map.unionsWithA \ys -> do
      let (ss, ps) = NonEmpty.unzip ys
      s <- maybeToEither ShapeConflict    $ allSame ss
      p <- maybeToEither PositionConflict $ Map.unionsWithA consistent ps
      return (s, p)

consistent :: NonEmpty Origins -> Maybe Origins
consistent = Multi.consistent . foldl1 Multi.intersection

maybeToEither :: e -> Maybe a -> Either e a
maybeToEither e = maybe (Left e) Right

-- TODO: do something with these conflicts.
data Conflict = ShapeConflict | PositionConflict
  deriving stock (Eq, Ord, Show)

-- TODO: before checking the realizability w.r.t. parametricity, it might be
-- good to check whether the type is inhabited. Especially in the case were
-- there are no examples, we should still be able to check automatically that
-- e.g. `{x : a} -> b` is not realizable.
-- TODO: check that this actually works as expected for multiple type variables.
check :: Problem -> Either Conflict [MorphExample]
check (Problem sig exs) = combine $ map (extendExample sig) exs

------ Refinements ------

-- TODO: how are refinements already used in synthesizers? Splitting up the search space is already often done in synthesizers, but not often is realizability used to rule out some options.

-- NOTE: perhaps a refinement is a choice made about a program that is
-- consistent with the specification, where "consistency" can be whatever we
-- want. In our case, consistency means that there is a partial function that
-- would make the program complete.


-- TODO: what if the refinement returns two problems (i.e. introducing multiple
-- holes)
-- TODO: what if a refinement can be applied in multiple ways?
-- TODO: maybe it should return [[Problem]], a sum of products.
-- TODO: even better, have it return some "lattice" of problems, somehow showing
-- the relations between all of them.
-- TODO: additionally, refinements might return
-- - missing/lifted examples (e.g. due to trace incompleteness)
-- - some usefulness measure (e.g. trace incompleteness might discourage
--   introducing foldr). Can we always statically determine the usefulness, or
--   should we first perform a realizability check?
-- - some information about how this refinement relates to/influences other
--   refinements
-- - a concrete sketch/some way to recover the final program from a series of
--   refinements
type Refinement = Problem -> [[Problem]]

introPair :: Refinement
introPair (Problem (sig@Signature { goal }) exs) = case goal of
  Tup t u -> return
    [ Problem sig { goal = t } $ exs <&> \(Example ins out) ->
      Example ins (getFst out)
    , Problem sig { goal = u } $ exs <&> \(Example ins out) ->
      Example ins (getSnd out)
    ]
  _ -> []
  where
    getFst (Pair a _) = a
    getFst _ = error "Type mismatch"
    getSnd (Pair _ b) = b
    getSnd _ = error "Type mismatch"

-- Randomly removes one variable from the context. How do we show the lattice
-- structure here?
-- TODO: how do we avoid multiple shrinkings leading to the same problem? We
-- could try to rely on some dynamic programming/caching technique, but perhaps
-- better would be to annotate variables in the context as being mandatory?
-- Still, it might be necessary to perform all possible shrinkings at once?
shrinkContext :: Refinement
shrinkContext (Problem sig@Signature { ctxt } exs) = [0 .. length ctxt - 1] <&> \n ->
  return $ Problem sig { ctxt = delete n ctxt } $ exs <&>
    \(Example ins out) -> Example (delete n ins) out
  where
    delete :: Int -> [a] -> [a]
    delete n xs = take n xs ++ drop (n + 1) xs

-- introFoldr :: Problem -> [Problem]
-- introFoldr (Problem sig exs) = _


------ Pretty Printing ------

-- TODO: can we pretty print Morph? It seems that we need the type information
-- to know which values should become variables, or alternatively Val should
-- contain some "magic" constructors for variables. Another alternative is to
-- print natural numbers to indicate the positions, but then it becomes
-- difficult to differentiate between having an Eq/Ord constraint or not.

prettyProblem :: Text -> Problem -> Doc ann
prettyProblem fun (Problem sig exs) = statements (header : examples)
  where
    header = sep [pretty fun, ":", pretty sig]
    examples = exs <&> \(Example ins out) -> sep
      (pretty fun : map (prettyExpr 3) ins ++ ["=", pretty out])

------

class    ToExpr a    where toVal :: a -> Expr h
instance ToExpr Int  where toVal = Lit . MkInt
instance ToExpr Bool where toVal = Lit . MkBool
instance ToExpr ()   where toVal = const Unit

instance ToExpr a => ToExpr [a] where
  toVal = MkList . map toVal

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

-- >>> printSignature sg
-- "(Eq a) => {x : a, xs : [a]} -> [a]"

-- >>> pretty $ extendExample sg ex
-- [a0, a1] | {a0} /= {a1} /= {a2} -> {a1} , [{a1}, {}] , -

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

-- >>> prettyProblem "test" prb
-- test : (None a) => {x : a, y : a, z : a} -> a
-- test 1 2 2 = 2
-- test 2 1 2 = 2
-- test 2 2 1 = 2

-- >>> check prb
-- Left PositionConflict

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

-- >>> prettyProblem "pair" pairExample
-- pair : (None a, None b) => {x : a, y : b} -> a * b
-- pair 1 True = 1 , True
-- pair False 3 = False , 3

introPairExample :: [[Problem]]
introPairExample = introPair pairExample

-- >>> fmap (fmap (prettyProblem "f")) introPairExample
-- [[f : (None a, None b) => {x : a, y : b} -> a
-- f 1 True = 1
-- f False 3 = False,f : (None a, None b) => {x : a, y : b} -> b
-- f 1 True = True
-- f False 3 = 3]]

sg1 :: Signature
sg1 = Signature [("a", Ord)] [("xs", List (Free "a"))] (List (Free "a"))

ex1 :: Example
ex1 = Example [toVal @[Int] [1,2,4,1,2,3,4,5,1,2]] (toVal @[Int] [1,2,3,4,5])

-- >>> let (m, _, _) = extendEx sg1 ex1 in pretty $ Map.lookup "a" m
-- {a0 = a3 = a8} <= {a1 = a4 = a9} <= {a5} <= {a2 = a6} <= {a7}
