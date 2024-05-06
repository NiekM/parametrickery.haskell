{-# LANGUAGE DuplicateRecordFields #-}

module Language.Container.Morphism where

import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.List qualified as List

import Base
import Data.Map.Multi (Multi)
import Data.Map.Multi qualified as Multi
import Data.Map.Utils qualified as Map
import Utils

import Language.Type
import Language.Expr
import Language.Container

type Origins = Multi Position Position

computeOrigins :: Ord a => Map Position a -> Map Position a -> Origins
computeOrigins p q = Multi.remapping (Multi.fromMap q) (Multi.fromMap p)

-- An input output example for container morphisms.
data MorphExample = MorphExample
  { relations :: Map Text Relation
  , shapeIns  :: [Expr Position]
  , shapeOut  :: Expr Position
  , origins   :: Map Text Origins
  } deriving stock (Eq, Ord, Show)

-- It seems that we only need to compute the relation for the inputs, since the
-- output values are a subset (and if they are not, this is already a conflict).
checkExample :: Signature -> Example -> Either Conflict MorphExample
checkExample (Signature vars ctxt goal) (Example ins out)
  | conflict  = Left PositionConflict
  | otherwise = Right $ MorphExample
    { relations = rs
    , shapeIns  = ss
    , shapeOut  = t
    , origins   = os
    }
  where
    RelContainer ss rs p = toRelContainer vars (snd <$> ctxt) ins
    Container t q = toContainer (fst <$> vars) goal out
    os = Map.intersectionWith computeOrigins p q
    conflict = any (isNothing . Multi.consistent) os

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

applyMorph :: Signature -> [MorphExample] -> [Expr Void] -> Maybe (Expr Void)
applyMorph (Signature vars ctxt _) m ins = case out of
  Nothing -> Nothing
  Just MorphExample { shapeOut, origins } -> fmap join $ shapeOut &
    traverse \p@Position { var } -> do
      os <- Map.lookup var origins
      q <- Set.lookupMin $ Multi.lookup p os
      positions <- Map.lookup var ps
      Map.lookup q positions
  where
    RelContainer ss rs ps = toRelContainer vars (snd <$> ctxt) ins
    out = m & List.find \MorphExample { shapeIns, relations } ->
      shapeIns == ss && relations == rs

-- TODO: do something with these conflicts.
data Conflict = ShapeConflict | PositionConflict
  deriving stock (Eq, Ord, Show)

------ Pretty ------

newtype PrettySet a = PrettySet { unPrettySet :: Set a }
  deriving newtype (Eq, Ord, Show)

instance Pretty a => Pretty (PrettySet a) where
  pretty = encloseSep lbrace rbrace ", "
    . map pretty
    . Set.toList
    . unPrettySet

instance Pretty MorphExample where
  pretty (MorphExample r s t o) =
    barred (inputs : relations) <+> "->" <+> pretty t'
    where
      t' = t <&> \p@(Position v _) -> case Map.lookup v o of
        Nothing -> error "Missing key"
        Just m -> PrettySet $ Multi.lookup p m
      inputs = sep (map (prettyExpr 3) s)
      relations = map pretty . filter (/= RelNone) $ Map.elems r
      barred = encloseSep mempty mempty " | "

instance Pretty Conflict where
  -- TODO: we can make this nicer
  pretty = viaShow
