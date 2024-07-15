-- TODO: perhaps rename to Language.Container.Example?
--       although it is a bit confusing...

{-# OPTIONS_GHC -Wno-orphans #-}
module Language.Container.Morphism where

import Data.List.NonEmpty qualified as NonEmpty
import Data.Set qualified as Set

import Base
import Data.Map.Multi (Multi)
import Data.Map.Multi qualified as Multi
import Data.Named
import Utils

import Language.Type
import Language.Expr
import Language.Container
import Language.Container.Relation

-- TODO: maybe rewrite with some other datatype?
type Origins = Multi Position Position

computeOrigins :: Ord a => Map Position a -> Map Position a -> Origins
computeOrigins p q = Multi.remapping (Multi.fromMap q) (Multi.fromMap p)
  & Multi.filterWithKey \k v -> k.var == v.var

-- A polymorphic input-output example, i.e. an input-output example for
-- container morphisms.
data PolyExample = PolyExample
  { inShapes  :: [Shape]
  , relations :: [Relation]
  , outShape  :: Shape
  , origins   :: Origins
  } deriving stock (Eq, Ord, Show)

-- It seems that we only need to compute the relation for the inputs, since the
-- output values are a subset (and if they are not, this is already a conflict).
-- TODO: currently, no type checking is performed, so some nonsensical programs
-- are considered realizable.
checkExample :: Signature -> Example -> Either Conflict PolyExample
checkExample
  Signature { constraints, context, goal }
  Example { inputs, output }
    | length types /= length inputs = Left ArgumentMismatch
    | not (Multi.consistent origins) = Left MagicOutput
    | otherwise = Right PolyExample { relations, inShapes, outShape, origins }
  where
    types        = map (.value) context
    inContainer  = toContainer (Product types) (Tuple inputs)
    outContainer = toContainer goal output
    outShape     = outContainer.shape
    origins      = computeOrigins inContainer.elements outContainer.elements
    relations    = computeRelations constraints inContainer.elements
    inShapes     = case inContainer.shape of
      Tuple s -> s
      _ -> error "Expected tuple"

-- | Combine multiple examples, checking if there are no conflicts.
combine :: [PolyExample] -> Either Conflict [PolyExample]
combine = traverse merge . NonEmpty.groupAllWith \example ->
  (example.inShapes, example.relations)
  where
    merge :: NonEmpty PolyExample -> Either Conflict PolyExample
    merge xs
      | not (allSame outShapes) = Left ShapeConflict
      | not (Multi.consistent origins) = Left PositionConflict
      | otherwise = Right (NonEmpty.head xs) { origins }
      where
        outShapes = fmap (.outShape) xs
        origins   = foldl1 Multi.intersection $ fmap (.origins) xs

-- TODO: do something with these conflicts.
data Conflict
  = ArgumentMismatch | ShapeConflict | MagicOutput | PositionConflict
  deriving stock (Eq, Ord, Show)

------ Pretty ------

instance Pretty (Hole (Set Position)) where
  pretty (MkHole ps) = case Set.toList ps of
    [x] -> pretty x
    xs  -> encloseSep lbrace rbrace ", " $ map pretty xs

instance Pretty PolyExample where
  pretty PolyExample { inShapes, relations, outShape, origins }
    | null inShapes = pretty outShape
    | otherwise = barred (inputs : rels) <+> "->" <+> output
    where
      output = pretty $ fmap (`Multi.lookup` origins) outShape
      inputs = sep (map pretty inShapes)
      rels = map pretty $ filter relevant relations
      barred = encloseSep mempty mempty " | "

instance Pretty (Named PolyExample) where
  pretty (Named name PolyExample { inShapes, relations, outShape, origins })
    | null rels = args <+> "=" <+> output
    | otherwise = args <+> encloseSep "| " " =" ", " rels <+> output
    where
      args = sep (pretty name : map pretty inShapes)
      rels = map pretty $ filter relevant relations
      output = pretty $ fmap (`Multi.lookup` origins) outShape

instance Pretty Conflict where
  pretty = viaShow
