module Language.Container where

import Data.Map.Strict qualified as Map
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
  (Free  v) x          -> return (v, x)
  Top       Unit       -> Unit
  (Tup t u) (Pair x y) -> Pair (poly t x) (poly u y)
  (Sum t _) (Inl x)    -> Inl (poly t x)
  (Sum _ u) (Inr y)    -> Inr (poly u y)
  (List  t) (Lst xs)   -> Lst (poly t <$> xs)
  (Base  _) (Lit x)    -> Lit x
  t x -> error . show $
    pretty (void x) <+> "does not have type" <+> pretty t <> "."

computePositions :: Mono -> Term -> State (Map Text Nat) (Expr (Position, Term))
computePositions t e = do
  poly t e & traverse \(v, x) -> do
    m <- get
    let n = fromMaybe 0 $ Map.lookup v m
    modify $ Map.insert v (n + 1)
    return (Position v n, x)

toContainer :: Mono -> Term -> Container
toContainer ty e = uncurry Container . extract $
  evalState (computePositions ty e) mempty

toContainers :: [(Mono, Term)] -> [Container]
toContainers xs = uncurry Container . extract <$>
  evalState (traverse (uncurry computePositions) xs) mempty

fromContainer :: Container -> Term
fromContainer Container { shape, positions } = case inject positions shape of
  Nothing -> error "Missing position"
  Just e -> accept e

------ Pretty ------

instance Pretty Position where
  pretty (Position a n) = pretty a <> pretty n

instance Pretty (Hole Position) where
  pretty (MkHole p) = pretty p

instance Pretty Container where
  pretty (Container s p) = pretty s <+> encloseSep lbrace rbrace ", " xs
    where
      xs = Map.assocs p <&> \(i, x) -> pretty i <+> "=" <+> pretty x
