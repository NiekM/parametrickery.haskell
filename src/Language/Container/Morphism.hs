module Language.Container.Morphism where

import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

import Base
import Data.Map.Multi (Multi)
import Data.Map.Multi qualified as Multi
import Utils

import Language.Type
import Language.Expr
import Language.Container
import Language.Container.Relation

type Origins = Multi Position Position

computeOrigins :: Ord a => Map Position a -> Map Position a -> Origins
computeOrigins p q = Multi.remapping (Multi.fromMap q) (Multi.fromMap p)

-- A polymorphic input-output example, i.e. an input-output example for
-- container morphisms.
data PolyExample = PolyExample
  { relations :: Map Text Relation
  , inShapes  :: [Shape]
  , outShape  :: Shape
  , origins   :: Origins
  } deriving stock (Eq, Ord, Show)

-- It seems that we only need to compute the relation for the inputs, since the
-- output values are a subset (and if they are not, this is already a conflict).
checkExample :: Signature -> Example -> Either Conflict PolyExample
checkExample (Signature vars ctxt goal) (Example ins out)
  | conflict  = Left PositionConflict
  | otherwise = Right PolyExample { relations, inShapes, outShape, origins }
  where
    Container outShape q = toContainer goal out

    inputs    = toContainers $ zip (snd <$> ctxt) ins
    inShapes  = shape <$> inputs
    p         = foldMap positions inputs

    relations = computeRelations vars p
    origins   = computeOrigins p q
    conflict  = isNothing $ Multi.consistent origins

combine :: [PolyExample] -> Either Conflict [PolyExample]
combine = traverse merge . NonEmpty.groupAllWith input
  where
    merge :: NonEmpty PolyExample -> Either Conflict PolyExample
    merge xs = do
      t <- maybeToEither ShapeConflict    $ allSame (outShape <$> xs)
      o <- maybeToEither PositionConflict $ consistent (origins <$> xs)
      return (NonEmpty.head xs) { outShape = t, origins = o }

    input :: PolyExample -> (Map Text Relation, [Shape])
    input PolyExample { relations, inShapes } = (relations, inShapes)

consistent :: NonEmpty Origins -> Maybe Origins
consistent = Multi.consistent . foldl1 Multi.intersection

-- applyMorph :: Signature -> [PolyExample] -> [Expr Void] -> Maybe (Expr Void)
-- applyMorph (Signature vars ctxt _) m ins = case out of
--   Nothing -> Nothing
--   Just PolyExample { outShape, origins } -> fmap join $ shapeOut &
--     traverse \p@Position { var } -> do
--       os <- Map.lookup var origins
--       q <- Set.lookupMin $ Multi.lookup p os
--       positions <- Map.lookup var ps
--       Map.lookup q positions
--   where
--     RelContainer ss rs ps = toRelContainer vars (snd <$> ctxt) ins
--     out = m & List.find \PolyExample { inShapes, relations } ->
--       shapeIns == ss && relations == rs

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

instance Pretty PolyExample where
  pretty (PolyExample _ [] t _) = pretty t
  pretty (PolyExample r s t o) =
    barred (inputs : relations) <+> "->" <+> pretty t'
    where
      t' = t <&> \p -> PrettySet $ Multi.lookup p o
      inputs = sep (map (prettyExpr 3) s)
      relations = map pretty . filter relevant $ Map.elems r
      barred = encloseSep mempty mempty " | "

instance Pretty Conflict where
  -- TODO: we can make this nicer
  pretty = viaShow
