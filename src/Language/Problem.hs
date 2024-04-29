module Language.Problem where

import Prettyprinter.Utils
import Base
import Language.Expr
import Language.Type
import Language.Container.Morphism

data Problem = Problem
  { sig :: Signature
  , exs :: [Example]
  } deriving stock (Eq, Ord, Show)

-- TODO: before checking the realizability w.r.t. parametricity, it might be
-- good to check whether the type is inhabited. Especially in the case were
-- there are no examples, we should still be able to check automatically that
-- e.g. `{x : a} -> b` is not realizable.
-- TODO: check that this actually works as expected for multiple type variables.
check :: Problem -> Either Conflict [MorphExample]
check (Problem sig exs) = combine $ map (extendExample sig) exs

instance Pretty Problem where
  pretty = prettyProblem "_"

prettyProblem :: Text -> Problem -> Doc ann
prettyProblem fun (Problem sig exs) = statements (header : examples)
  where
    header = sep [pretty fun, ":", pretty sig]
    examples = exs <&> \(Example ins out) -> sep
      (pretty fun : map (prettyExpr 3) ins ++ ["=", pretty out])
