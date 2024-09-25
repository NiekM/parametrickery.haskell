module Language.Container.Relation
  ( Relation(..)
  , computeRelations
  , relevant
  , checkRelation
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

computeRelation :: Map Position Term -> Constraint -> Relation
computeRelation p = \case
  Eq  a -> RelEq . Set.fromList $ order a p
  Ord a -> RelOrd $ order a p

computeRelations :: [Constraint] -> Map Position Term -> [Relation]
computeRelations cs p = cs <&> computeRelation p

ordered :: Ord a => [a] -> Bool
ordered [] = True
ordered (x:xs) = and $ zipWith (<) (x:xs) xs

checkRelation :: Map Position Term -> Relation -> Bool
checkRelation elements = \case
  RelEq r ->
    let q = Set.map (Set.map (elements Map.!?)) r
    in all ((== 1) . Set.size) q && Set.size q == Set.size r
  RelOrd r ->
    let q = map (Set.map (elements Map.!?)) r
    in all ((== 1) . Set.size) q && ordered q

------ Pretty ------

eqClass :: Pretty a => Set a -> Doc ann
eqClass s = case Set.toList s of
  [x] -> pretty x
  xs  -> encloseSep mempty mempty " == " $ map pretty xs

instance Pretty Relation where
  pretty = \case
    RelEq  eq  -> encloseSep mempty mempty " /= " . fmap eqClass $ Set.toList eq
    RelOrd ord -> encloseSep mempty mempty " < "  $ fmap eqClass ord
