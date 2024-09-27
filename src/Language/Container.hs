module Language.Container where

import Data.Map.Strict qualified as Map
import Data.List qualified as List
import Control.Carrier.Reader
import Control.Carrier.State.Lazy

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
poly :: Has (Reader Context) sig m =>
  Mono -> Expr a -> m (Expr (Text, Expr a))
poly = \cases
  (Free v) x -> return $ return (v, x)
  (Product ts) (Tuple xs) -> Tuple <$> zipWithM poly ts xs
  (Data d ts) (Ctr c x) -> do
    cs <- asks $ getConstructors d ts
    case List.find (\ct -> ct.name == c) cs of
      Nothing -> error . show $ "Datatype" <+> pretty d
        <+> "does not have a constructor" <+> pretty c <> "."
      Just ct -> Ctr c <$> poly ct.field x
  (Base _) (Lit x) -> return $ Lit x
  t x -> error . show $
    pretty (void x) <+> "does not have type" <+> pretty t <> "."

computePositions :: Expr (Text, Term) -> Expr (Position, Term)
computePositions e = run $ evalState @(Map Text Nat) mempty do
  forM e \(v, x) -> do
    m <- get
    let n = fromMaybe 0 $ Map.lookup v m
    modify $ Map.insert v (n + 1)
    return (Position v n, x)

toContainer :: Has (Reader Context) sig m => Mono -> Term -> m Container
toContainer t = fmap (uncurry Container . extract . computePositions) . poly t

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
