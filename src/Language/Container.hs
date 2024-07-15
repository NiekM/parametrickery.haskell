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
  { shape    :: Shape
  , elements :: Map Position Term
  } deriving stock (Eq, Ord, Show)

-- Traverse an expression along with its type, introducing holes at free
-- variables.
poly :: Mono -> Expr a -> Expr (Text, Expr a)
poly = \cases
  (Free v) x -> return (v, x)
  (Product ts) (Tuple xs) -> Tuple $ zipWith poly ts xs
  (Sum ts) (Proj i n x) -> Proj i n $ poly (ts !! fromIntegral i) x
  (List t) (Lst xs) -> Lst (poly t <$> xs)
  (Base _) (Lit x) -> Lit x
  t x -> error . show $
    pretty (void x) <+> "does not have type" <+> pretty t <> "."

computePositions :: Mono -> Term -> Expr (Position, Term)
computePositions t e = flip evalState mempty do
  poly t e & traverse \(v, x) -> do
    m <- get
    let n = fromMaybe 0 $ Map.lookup v m
    modify $ Map.insert v (n + 1)
    return (Position v n, x)

toContainer :: Mono -> Term -> Container
toContainer t = uncurry Container . extract . computePositions t

fromContainer :: Container -> Term
fromContainer Container { shape, elements } = case inject elements shape of
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
