module Language.Container.Relation
  ( Relation(..)
  , computeRelations
  ) where

import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

import Base

import Language.Type
import Language.Expr
import Language.Container

-- The container representation of type class relations.
data Relation
  = RelNone
  -- | Sets of equivalence classes
  | RelEq  (Set (Set Position))
  -- | Ordered equivalence classes
  | RelOrd [Set Position]
  deriving stock (Eq, Ord, Show)

-- We assume that all positions in the map have the same type.
computeRelation :: Class -> Map Position Term -> Relation
computeRelation c ps = case c of
  None -> RelNone
  Eq   -> RelEq $ Set.fromList order
  Ord  -> RelOrd order
  where
    order = fmap (Set.fromList . NonEmpty.toList . fmap fst)
      . NonEmpty.groupWith snd . List.sortOn snd . Map.assocs $ ps

computeRelations :: [(Text, Class)] -> Map Position Term -> Map Text Relation
computeRelations cs p = Map.fromList $ cs <&>
  \(v, c) -> (v,) . computeRelation c $ p &
    Map.filterWithKey \Position { var } _ -> v == var

eqClass :: Pretty a => Set a -> Doc ann
eqClass = encloseSep lbrace rbrace " = " . map pretty . Set.toList

instance Pretty Relation where
  pretty = \case
    RelNone -> "{}"
    RelEq  eq  -> encloseSep mempty mempty " /= " . fmap eqClass $ Set.toList eq
    RelOrd ord -> encloseSep mempty mempty " <= " $ fmap eqClass ord
