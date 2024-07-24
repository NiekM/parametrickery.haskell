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

data Pattern = Pattern
  { shapes    :: [Shape]
  , relations :: [Relation]
  } deriving stock (Eq, Ord, Show)

-- A polymorphic input-output example, i.e. an input-output example for
-- container morphisms.
data PolyExample = PolyExample
  { input   :: Pattern
  , output  :: Shape
  , origins :: Origins
  } deriving stock (Eq, Ord, Show)

-- It seems that we only need to compute the relation for the inputs, since the
-- output values are a subset (and if they are not, this is already a conflict).
-- TODO: currently, no type checking is performed, so some nonsensical programs
-- are considered realizable.
checkExample :: Signature -> Example -> Either Conflict PolyExample
checkExample signature example
    | length types /= length example.inputs = Left ArgumentMismatch
    | not (Multi.consistent origins) = Left MagicOutput
    | otherwise = Right PolyExample
      { output = output.shape
      , input  = Pattern (unTuple input.shape) relations
      , origins
      }
  where
    types     = map (.value) signature.context
    input     = toContainer (Product types) (Tuple example.inputs)
    output    = toContainer signature.goal example.output
    relations = computeRelations signature.constraints input.elements
    origins   = computeOrigins input.elements output.elements

    unTuple (Tuple xs) = xs
    unTuple _ = error "Expected tuple"

-- | Combine multiple examples, checking if there are no conflicts.
combine :: [PolyExample] -> Either Conflict [PolyExample]
combine = traverse merge . NonEmpty.groupAllWith (.input)
  where
    merge :: NonEmpty PolyExample -> Either Conflict PolyExample
    merge xs
      | not (allSame outputs) = Left ShapeConflict
      | not (Multi.consistent origins) = Left PositionConflict
      | otherwise = Right (NonEmpty.head xs) { origins }
      where
        outputs = fmap (.output) xs
        origins = foldl1 Multi.intersection $ fmap (.origins) xs

-- TODO: do something with these conflicts.
data Conflict
  = ArgumentMismatch | ShapeConflict | MagicOutput | PositionConflict
  deriving stock (Eq, Ord, Show)

------ Pretty ------

instance Pretty (Hole (Set Position)) where
  pretty (MkHole ps) = case Set.toList ps of
    [x] -> pretty x
    xs  -> encloseSep lbrace rbrace ", " $ map pretty xs

instance Pretty Pattern where
  pretty patt
    | null relations = inputs
    | otherwise = inputs <+> "|" <+>
      concatWith (surround ", ") (pretty <$> relations)
    where
      inputs = sep (map pretty patt.shapes)
      relations = filter relevant patt.relations

instance Pretty PolyExample where
  pretty PolyExample { input, output, origins }
    | null input.shapes = pretty output
    | otherwise = pretty input <+> "->" <+> out
    where
      out = pretty $ fmap (`Multi.lookup` origins) output

instance Pretty (Named PolyExample) where
  pretty (Named name PolyExample { input, output, origins })
    | null input.shapes = pretty name <+> "=" <+> out
    | otherwise = pretty name <+> pretty input <+> "=" <+> out
    where
      out = pretty $ fmap (`Multi.lookup` origins) output

instance Pretty Conflict where
  pretty = viaShow
