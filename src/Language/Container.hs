module Language.Container where

import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Control.Monad.State

import Base
import Data.Map.Multi (Multi)
import Data.Map.Multi qualified as Multi

import Language.Type
import Language.Expr

data Position = Position { var :: Text, pos :: Nat }
  deriving stock (Eq, Ord, Show)

data Container = Container
  { shape     :: Expr
  , positions :: Map Text (Map Position Expr)
  } deriving stock (Eq, Ord, Show)

toContainer :: [Text] -> Mono -> Expr -> Container
toContainer as ty e = evalState (extend ty e) st
  where
    st :: Map Text Nat
    st = Map.fromList $ as <&> \v -> (v, 0)

    extend :: Mono -> Expr -> State (Map Text Nat) Container
    extend = \cases
      (Free v) x -> do
        m <- get
        case Map.lookup v m of
          Nothing -> error "Missing variable counter!"
          Just n -> do
            put $ Map.adjust (+1) v m
            let pos = Position v n
            let shape = Lit (MkText (Text.pack . show $ pos))
            return . Container shape . Map.singleton v $ Map.singleton pos x
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
      (Base _) x -> return $ Container x mempty
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

computeRelation :: Class -> Map Position Expr -> Relation
computeRelation c ps = case c of
  None -> RelNone
  Eq   -> RelEq $ Set.fromList order
  Ord  -> RelOrd order
  where
    order = map (Set.fromList . map fst)
      . List.groupBy ((==) `on` snd)
      . List.sortOn snd
      $ Map.assocs ps

type Origins = Multi Position Position

computeOrigins :: Map Position Expr -> Map Position Expr -> Origins
computeOrigins p q = Multi.remapping (Multi.fromMap q) (Multi.fromMap p)

-- An input output example for container morphisms.
data MorphExample = MorphExample
  { relations :: Map Text Relation
  , shapeIn   :: Expr
  , shapeOut  :: Expr
  , origins   :: Map Text Origins
  } deriving stock (Eq, Ord, Show)

-- It seems that we only need to compute the relation for the inputs, since the
-- output values are a subset (and if they are not, this is already a conflict).
extendExample :: Signature -> Example -> MorphExample
extendExample (Signature vars ctxt goal) (Example ins out) =
  MorphExample r s t (Map.intersectionWith computeOrigins p q)
  where
    -- TODO: is it really the best to turn them into a tuple? perhaps we should
    -- undo the tupling afterwards so that we have a list of input shapes. we
    -- should be careful however to only untuple as much as we tupled.
    i = foldr Tup Top $ map snd ctxt
    x = foldr Pair Unit ins
    Container t p = toContainer (fst <$> vars) i x
    Container s q = toContainer (fst <$> vars) goal out
    r = Map.intersectionWith computeRelation (Map.fromList vars) p

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

-- instance Pretty MorphExample where
--   pretty (MorphExample r s t o) = _
