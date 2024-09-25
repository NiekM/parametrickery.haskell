-- TODO: perhaps rename to Language.Container.Example?
--       although it is a bit confusing...

{-# OPTIONS_GHC -Wno-orphans #-}
module Language.Container.Morphism where

import Data.List.NonEmpty qualified as NonEmpty
import Data.Map qualified as Map
import Data.Set qualified as Set

import Control.Applicative
import Data.Monoid (Alt(..))

import Base
import Data.Map.Multi (Multi)
import Data.Map.Multi qualified as Multi
import Data.Named

import Language.Type
import Language.Expr
import Language.Declaration
import Language.Container
import Language.Container.Relation
import Prettyprinter.Utils
import Utils

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
checkExample :: [Datatype] -> Signature -> Example
  -> Either Conflict PolyExample
checkExample defs signature example
  | length types /= length example.inputs =
    Left $ ArgumentMismatch types example.inputs
  | not (Multi.consistent result.origins) =
    Left $ MagicOutput Declaration { signature, bindings = [example] }
  | otherwise = return result
  where
    types = map (.value) signature.context
    input = toContainer defs (Product types) (Tuple example.inputs)
    output = toContainer defs signature.goal example.output
    relations = computeRelations signature.constraints input.elements
    shapes = projections input.shape

    result = PolyExample
      { input   = Pattern shapes relations
      , output  = output.shape
      , origins = computeOrigins input.elements output.elements
      }

-- | Combine multiple examples, checking if there are no conflicts.
combine :: [PolyExample] -> Either Conflict [PolyExample]
combine = traverse merge . NonEmpty.groupAllWith (.input)
  where
    merge :: NonEmpty PolyExample -> Either Conflict PolyExample
    merge examples = case grouped of
      (result :| [])
        | Multi.consistent result.origins -> return result
        | otherwise -> Left $ PositionConflict (NonEmpty.nub examples)
      _ -> Left $ ShapeConflict grouped
      where
        grouped = intersect <$> NonEmpty.groupAllWith1 (.output) examples

    intersect :: NonEmpty PolyExample -> PolyExample
    intersect examples@(example :| _) = example
      { origins = foldl1 Multi.intersection $ fmap (.origins) examples }

-- TODO: do something with these conflicts.
data Conflict
  = ArgumentMismatch [Mono] [Term]
  | ShapeConflict (NonEmpty PolyExample)
  | MagicOutput Problem
  | PositionConflict (NonEmpty PolyExample)
  deriving stock (Eq, Ord, Show)

type PolyProblem = Declaration PolyExample

-- TODO: before checking the realizability w.r.t. parametricity, it might be
-- good to check whether the type is inhabited. Especially in the case were
-- there are no examples, we should still be able to check automatically that
-- e.g. `{x : a} -> b` is not realizable.
check :: [Datatype] -> Problem -> Either Conflict PolyProblem
check defs (Declaration signature exs) = do
  bindings <- combine =<< mapM (checkExample defs signature) exs
  return Declaration { signature, bindings }

altMap :: (Foldable f, Alternative m) => (a -> m b) -> f a -> m b
altMap f = getAlt . foldMap (Alt . f)

matchShape :: Shape -> Term -> Maybe (Map Position Term)
matchShape (Tuple xs) (Tuple ys) = Map.unions <$> zipWithM matchShape xs ys
matchShape (Ctr c x) (Ctr d y) | c == d = matchShape x y
matchShape (Lit i) (Lit j) | i == j = Just Map.empty
matchShape (Hole (MkHole p)) x = Just $ Map.singleton p x
matchShape _ _ = Nothing

matchPattern :: Pattern -> [Term] -> Maybe (Map Position Term)
matchPattern patt terms = do
  elements <- Map.unions <$> zipWithM matchShape patt.shapes terms
  guard $ all (checkRelation elements) patt.relations
  return elements

applyExample :: PolyExample -> [Term] -> Maybe Term
applyExample example terms = do
  inElements <- matchPattern example.input terms
  outElements <-
    Multi.toMap $ Multi.compose (Multi.fromMap inElements) example.origins
  accept <$> inject outElements example.output

applyProblem :: PolyProblem -> [Term] -> Maybe Term
applyProblem problem terms = altMap (`applyExample` terms) problem.bindings

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
      inputs = sep (map prettyMaxPrec patt.shapes)
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
  pretty = \case
    ArgumentMismatch ts es -> "ArgumentMismatch!" <+> indent 2
      (vcat [pretty ts, pretty es])
    ShapeConflict xs -> "ShapeConflict!" <+> indent 2 (pretty xs)
    MagicOutput x -> "MagicOutput!" <+> indent 2 (pretty x)
    PositionConflict xs -> "PositionConflict!" <+> indent 2 (pretty xs)
