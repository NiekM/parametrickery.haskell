module Refinements where

import Base
import Language.Type
import Language.Expr
import Language.Problem

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

introElimPair :: Refinement
introElimPair (Problem (sig@Signature { goal }) exs) = case goal of
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

-- introAnyFoldr :: Refinement
-- introAnyFoldr (Problem  exs) = _

-- introFoldr :: [Expr h] -> Refinement
-- introFoldr xs (Problem sig exs) = _
