module Language.Container where

import Data.Map.Strict qualified as Map
import Control.Carrier.Reader
import Control.Carrier.State.Lazy

import Base
import Utils

import Language.Type
import Language.Expr

type Position = Named Nat

type Shape = Term Position

-- TODO: maybe try to rework this to use IntMap, as it is much more efficient.
data Container = Container
  { shape    :: Shape
  , elements :: Map Position Value
  } deriving stock (Eq, Ord, Show)

-- Traverse an expression along with its type, introducing holes at free
-- variables.
poly :: Has (Reader Context) sig m => Mono -> Term a -> m (Term (Name, Term a))
poly = \cases
  (Free v) x -> return $ return (v, x)
  (Product ts) (Tuple xs) -> Tuple <$> zipWithM poly ts xs
  (Data d ts) (Ctr c x) -> do
    cs <- asks $ getConstructors d ts
    case find c cs of
      Nothing -> error . show $ "Datatype" <+> pretty d
        <+> "does not have a constructor" <+> pretty c <> "."
      Just ct -> Ctr c <$> poly ct x
  (Base _) (Lit x) -> return $ Lit x
  t x -> error $
    show (void x) <> " does not have type " <> show t <> "."

computePositions :: Term (Name, Value) -> Term (Position, Value)
computePositions e = run $ evalState @(Map Name Nat) mempty do
  forM e \(v, x) -> do
    m <- get
    let n = fromMaybe 0 $ Map.lookup v m
    modify $ Map.insert v (n + 1)
    return (Named v n, x)

toContainer :: Has (Reader Context) sig m => Mono -> Value -> m Container
toContainer t = fmap (uncurry Container . extract . computePositions) . poly t

fromContainer :: Container -> Value
fromContainer Container { shape, elements } = case inject elements shape of
  Nothing -> error "Missing position"
  Just e -> accept e
