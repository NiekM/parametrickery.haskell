{-# LANGUAGE UndecidableInstances #-}

module Language.Declaration where

import Prettyprinter.Utils
import Base
import Language.Expr
import Language.Type
import Language.Container.Morphism

-- | A declaration consists of a signature with some bindings.
-- TODO: should this maybe be a nonempty amount of bindings?
data Declaration binding = Declaration
  { signature :: Signature
  , bindings  :: [binding]
  } deriving stock (Eq, Ord, Show)

type Problem = Declaration Example
type PolyProblem = Declaration PolyExample

-- TODO: before checking the realizability w.r.t. parametricity, it might be
-- good to check whether the type is inhabited. Especially in the case were
-- there are no examples, we should still be able to check automatically that
-- e.g. `{x : a} -> b` is not realizable.
-- TODO: check that this actually works as expected for multiple type variables.
check :: Problem -> Result PolyProblem
check (Declaration signature exs) = do
  bindings <- combine =<< mapM (checkExample signature) exs
  return Declaration { signature, bindings }

-- -- | Replace an argument with the result of its recursive call.
-- -- TODO: not sure if this makes sense
-- recurse :: Text -> PolyProblem -> PolyProblem
-- recurse = _

instance Pretty (Named binding) => Pretty (Declaration binding) where
  pretty = prettyNamed "_"
 
instance Pretty (Named binding) => Pretty (Named (Declaration binding)) where
  pretty (Named name (Declaration sig exs)) =
    statements (prettyNamed name sig : map (prettyNamed name) exs)
 