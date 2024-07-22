{-# LANGUAGE UndecidableInstances #-}

module Language.Declaration where

import Control.Applicative
import Data.Monoid (Alt(..))

import Prettyprinter.Utils
import Base
import Data.Map.Multi qualified as Multi
import Data.Named
import Language.Expr
import Language.Type
import Language.Container
import Language.Container.Relation
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

-- Morphism appplication functions

-- TODO: check if this behaves as expected
-- It is a bit random that this one works on Containers and applyExamples works
-- on Terms.
applyExample :: Container -> [Relation] -> PolyExample -> Maybe Container
applyExample input rels PolyExample { relations, inShapes, outShape, origins }
  | Tuple inShapes == input.shape
  , relations == rels
  , Just outPos <- outPositions = Just Container
    { shape = outShape
    , elements = outPos
    }
  | otherwise = Nothing
  where
    outPositions =
      Multi.toMap $ Multi.compose (Multi.fromMap input.elements) origins

altMap :: (Foldable f, Alternative m) => (a -> m b) -> f a -> m b
altMap f = getAlt . foldMap (Alt . f)

applyPoly :: Container -> PolyProblem -> Maybe Container
applyPoly container Declaration { signature, bindings } =
  altMap (applyExample container relations) bindings
  where relations = computeRelations signature.constraints container.elements
