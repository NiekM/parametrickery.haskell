module Refinements where

import Base
import Language.Type
import Language.Expr
import Language.Problem

import Utils

------ Refinements ------

-- TODO: how are refinements already used in synthesizers? Splitting up the search space is already often done in synthesizers, but not often is realizability used to rule out some options.

{-

What exactly do we expect from a refinement?

- It is a choice/assumption made about a program that is consistent with the
  specification, where "consistency" in our case means that there exists a
  (partial) function that would complete the program.
- Refinements can be applied in multiple ways.
- Refinements can introduce multiple new problems.
- Refinements can have some relation to other refinements (perhaps a lattice
  structure should be inherent to the refinements?).
- Should they take into account missing examples (e.g. due to trace
  completeness?)
- some usefulness measure (e.g. trace incompleteness might discourage
  introducing foldr). Can we always statically determine the usefulness, or
  should we first perform a realizability check?
- some information about how this refinement relates to/influences other
  refinements
- a concrete sketch/some way to recover the final program from a series of
  refinements
- Should refinements be able to introduce new (fresh) variables?

-}


type Refinement = Problem -> [[Problem]]

-- NOTE: this is mostly a test refinement. I don't know how precise we have to
-- get with the refinements. It could be interesting to keep refining until a
-- program is solved, but more realistic is to perform a refinement, then first
-- use a realizability technique as well as some usefulness measure to decide
-- whether to continue refining or call an external synthesizer.
introPair :: Refinement
introPair (Problem (sig@Signature { goal }) exs) = case goal of
  Tup t u -> return
    [ Problem sig { goal = t } $ exs <&> \case
      Example ins (Pair a _) -> Example ins a
      _ -> error "Type mismatch"
    , Problem sig { goal = u } $ exs <&> \case
      Example ins (Pair _ b) -> Example ins b
      _ -> error "Type mismatch"
    ]
  _ -> []

-- Randomly removes one variable from the context. How do we show the lattice
-- structure here?
-- TODO: how do we avoid multiple shrinkings leading to the same problem? We
-- could try to rely on some dynamic programming/caching technique, but perhaps
-- better would be to annotate variables in the context as being mandatory?
-- Still, it might be necessary to perform all possible shrinkings at once?
shrinkContext :: Refinement
shrinkContext p = pickApart p <&> \(_, _, _, q) -> [q]

elimList :: Refinement
elimList p = pickApart p & mapMaybe
  \(v, t, es, Problem s@(Signature { ctxt }) xs) -> case t of
    List u ->
      let
        (nil, cons) = zip es xs & mapEither \case
          (Lst [], ex) -> Left ex
          (Lst (y:ys), Example ins out) ->
            Right $ Example (y : Lst ys : ins) out
          _ -> error "Expected a list!"
      in Just
        [ Problem s nil
        -- TODO: generate fresh variables
        , Problem s { ctxt = (v <> "_h", u) : (v <> "_t", List u) : ctxt } cons
        ]
    _ -> Nothing

-- introAnyFoldr :: Refinement
-- introAnyFoldr (Problem  exs) = _

-- introFoldr :: [Expr h] -> Refinement
-- introFoldr xs (Problem sig exs) = _
