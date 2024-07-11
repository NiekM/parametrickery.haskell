module Language.Container.Relation
  ( Relation(..)
  , computeRelations
  , relevant
  ) where

import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

import Base

import Language.Type
import Language.Expr
import Language.Container

-- | The container representation of type class relations.
data Relation
  -- | Sets of equivalence classes.
  = RelEq (Set (Set Position))
  -- | Ordered equivalence classes.
  | RelOrd [Set Position]
  deriving stock (Eq, Ord, Show)

-- | A relation is only relevant if it has at least 2 elements.
relevant :: Relation -> Bool
relevant = \case
  RelEq  eq  -> Set.size (Set.unions eq ) > 1
  RelOrd ord -> Set.size (Set.unions ord) > 1

order :: Text -> Map Position Term -> [Set Position]
order a
  = fmap (Set.fromList . NonEmpty.toList . fmap fst)
  . NonEmpty.groupAllWith snd
  . Map.assocs
  . Map.filterWithKey \Position { var } _ -> a == var

computeRelations :: [Constraint] -> Map Position Term -> [Relation]
computeRelations cs p = cs <&> \case
  Eq  a -> RelEq . Set.fromList $ order a p
  Ord a -> RelOrd $ order a p

------ Pretty ------

eqClass :: Pretty a => Set a -> Doc ann
eqClass s = case Set.toList s of
  [x] -> pretty x
  xs  -> encloseSep mempty mempty " == " $ map pretty xs

instance Pretty Relation where
  pretty = \case
    RelEq  eq  -> encloseSep mempty mempty " /= " . fmap eqClass $ Set.toList eq
    RelOrd ord -> encloseSep mempty mempty " < "  $ fmap eqClass ord
