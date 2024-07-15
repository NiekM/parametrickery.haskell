{-# LANGUAGE UndecidableInstances #-}

module Language.Declaration where

import Prettyprinter.Utils
import Base
import Data.Named
import Language.Expr
import Language.Type
import Language.Container.Morphism

-- | A declaration consists of a signature with some bindings.
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
check :: Problem -> Either Conflict PolyProblem
check (Declaration signature exs) = do
  bindings <- combine =<< mapM (checkExample signature) exs
  return Declaration { signature, bindings }

instance Pretty (Named binding) => Pretty (Declaration binding) where
  pretty = prettyNamed "_"
 
instance Pretty (Named binding) => Pretty (Named (Declaration binding)) where
  pretty (Named name (Declaration sig exs)) =
    statements (prettyNamed name sig : map (prettyNamed name) exs)
 