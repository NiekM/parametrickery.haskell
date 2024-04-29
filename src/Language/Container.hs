module Language.Container where

import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Control.Monad.State

import Base

import Language.Type
import Language.Expr

data Position = Position { var :: Text, pos :: Nat }
  deriving stock (Eq, Ord, Show)

data Container = Container
  { shape     :: Expr Position
  , positions :: Map Text (Map Position (Expr Void))
  } deriving stock (Eq, Ord, Show)

toContainer :: [Text] -> Mono -> Expr Void -> Container
toContainer as ty e = evalState (extend ty e) st
  where
    st :: Map Text Nat
    st = Map.fromList $ as <&> \v -> (v, 0)

    extend :: Mono -> Expr Void -> State (Map Text Nat) Container
    extend = \cases
      (Free v) x -> do
        m <- get
        case Map.lookup v m of
          Nothing -> error "Missing variable counter!"
          Just n -> do
            put $ Map.adjust (+1) v m
            let p = Position v n
            return . Container (Hole p) . Map.singleton v $ Map.singleton p x
      Top Unit -> return $ Container Unit mempty
      (Tup t u) (Pair x y) -> do
        Container s p <- extend t x
        Container r q <- extend u y
        return $ Container (Pair s r) $ Map.unionWith Map.union p q
      (Sum t _) (Inl x) -> do
        Container s p <- extend t x
        return $ Container (Inl s) p
      (Sum _ u) (Inr y) -> do
        Container s p <- extend u y
        return $ Container (Inr s) p
      (List t) (MkList xs) -> do
        r <- forM xs $ extend t
        let (ss, ps) = unzip [ (s, p) | Container s p <- r]
        return $ Container (MkList ss) $ Map.unionsWith Map.union ps
      (Base _) (Lit x) -> return $ Container (Lit x) mempty
      t x -> error . show $
        "Mismatching types!" <+> pretty x <+> ":/:" <+> pretty t

-- The container representation of type class relations.
data Relation
  = RelNone
  -- | Sets of equivalence classes
  | RelEq  (Set (Set Position))
  -- | Ordered equivalence classes
  | RelOrd [Set Position]
  deriving stock (Eq, Ord, Show)

computeRelation :: Ord h => Class -> Map Position (Expr h) -> Relation
computeRelation c ps = case c of
  None -> RelNone
  Eq   -> RelEq $ Set.fromList order
  Ord  -> RelOrd order
  where
    order = map (Set.fromList . map fst)
      . List.groupBy ((==) `on` snd)
      . List.sortOn snd
      $ Map.assocs ps

------ Pretty ------

instance Pretty Position where
  pretty (Position a n) = pretty a <> pretty n

instance Pretty Container where
  pretty (Container s p) = pretty s <+> encloseSep lbrace rbrace ", " xs
    where
      xs = map (\(i, x) -> pretty i <+> "=" <+> pretty x)
        . Map.assocs
        . Map.unions
        . map snd
        $ Map.assocs p

eqClass :: Pretty a => Set a -> Doc ann
eqClass = encloseSep lbrace rbrace " = " . map pretty . Set.toList

instance Pretty Relation where
  pretty = \case
    RelNone -> "{}"
    RelEq  eq  -> encloseSep mempty mempty " /= " . fmap eqClass $ Set.toList eq
    RelOrd ord -> encloseSep mempty mempty " <= " $ fmap eqClass ord
