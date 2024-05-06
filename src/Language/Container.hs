{-# LANGUAGE DuplicateRecordFields #-}

module Language.Container where

import Data.List.NonEmpty qualified as NonEmpty
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Control.Monad.State

import Base
import Utils

import Language.Type
import Language.Expr

data Position = Position { var :: Text, pos :: Nat }
  deriving stock (Eq, Ord, Show)

type Shape = Expr Position

-- TODO: maybe try to rework this to use IntMap, as it is much more efficient.
data Container = Container
  { shape     :: Shape
  , positions :: Map Position Term
  } deriving stock (Eq, Ord, Show)

-- Traverse an expression along with its type, introducing holes at free
-- variables.
poly :: Mono -> Expr a -> Expr (Text, Expr a)
poly = \cases
  (Free  v) x          -> Hole (v, x)
  Top       Unit       -> Unit
  (Tup t u) (Pair x y) -> Pair (poly t x) (poly u y)
  (Sum t _) (Inl x)    -> Inl (poly t x)
  (Sum _ u) (Inr y)    -> Inr (poly u y)
  (List  t) (Lst xs)   -> Lst (poly t <$> xs)
  (Base  _) (Lit x)    -> Lit x
  t x -> error . show $
    "Mismatching types!" <+> pretty (() <$ x) <+> ":/:" <+> pretty t

computePositions :: Mono -> Term -> State (Map Text Nat) (Expr (Position, Term))
computePositions t e = do
  poly t e & traverse \(v, x) -> do
    m <- get
    let n = fromMaybe 0 $ Map.lookup v m
    modify $ Map.insert v (n + 1)
    return (Position v n, x)

toContainer :: Mono -> Term -> Container
toContainer ty e = Container shape pos
  where (pos, shape) = extract $ evalState (computePositions ty e) mempty

toContainers :: [(Mono, Term)] -> ([Shape], Map Position Term)
toContainers xs = (p, ss)
  where
    (ss, p) = traverse extract $
      evalState (traverse (uncurry computePositions) xs) mempty

-- The container representation of type class relations.
data Relation
  = RelNone
  -- | Sets of equivalence classes
  | RelEq  (Set (Set Position))
  -- | Ordered equivalence classes
  | RelOrd [Set Position]
  deriving stock (Eq, Ord, Show)

computeRelation :: Ord h => Class -> [(Position, Expr h)] -> Relation
computeRelation c ps = case c of
  None -> RelNone
  Eq   -> RelEq $ Set.fromList order
  Ord  -> RelOrd order
  where
    order = fmap (Set.fromList . NonEmpty.toList . fmap fst)
      . NonEmpty.groupWith snd . List.sortOn snd $ ps

-- TODO: it is a bit weird that normal containers have one shape, but containers
-- with relations have multiple.
data RelContainer = RelContainer
  { shapes    :: [Shape]
  , relations :: Map Text Relation
  , positions :: Map Position Term
  } deriving stock (Eq, Ord, Show)

toRelContainer :: [(Text, Class)] -> [Mono] -> [Term] -> RelContainer
toRelContainer vars ts es = RelContainer { shapes, relations, positions }
  where
    (shapes, positions) = toContainers (zip ts es)

    relations = Map.intersectionWith computeRelation (Map.fromList vars) ps

    ps = Map.fromList $ NonEmpty.groupWith (var . fst) (Map.assocs positions)
      <&> \xs -> (var . fst $ NonEmpty.head xs, NonEmpty.toList xs)

------ Pretty ------

instance Pretty Position where
  pretty (Position a n) = pretty a <> pretty n

instance Pretty Container where
  pretty (Container s p) = pretty s <+> encloseSep lbrace rbrace ", " xs
    where
      xs = Map.assocs p <&> \(i, x) -> pretty i <+> "=" <+> pretty x

eqClass :: Pretty a => Set a -> Doc ann
eqClass = encloseSep lbrace rbrace " = " . map pretty . Set.toList

instance Pretty Relation where
  pretty = \case
    RelNone -> "{}"
    RelEq  eq  -> encloseSep mempty mempty " /= " . fmap eqClass $ Set.toList eq
    RelOrd ord -> encloseSep mempty mempty " <= " $ fmap eqClass ord
