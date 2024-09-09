module Language.Container where

import Data.Map.Strict qualified as Map
import Control.Monad.State
import Data.List qualified as List

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

getConstructors :: Text -> [Mono] -> [Datatype] -> [Constructor]
getConstructors d ts defs = case List.find (\dt -> dt.name == d) defs of
  Nothing -> error . show $ "Datatype" <+> pretty d <+> "does not exist."
  Just dt -> dt.constructors <&> \(Constructor c fields) ->
    Constructor c (fields & instantiate (Map.fromList $ zip dt.arguments ts))

-- Traverse an expression along with its type, introducing holes at free
-- variables.
poly :: [Datatype] -> Mono -> Expr a -> Expr (Text, Expr a)
poly defs = \cases
  (Free v) x -> return (v, x)
  (Product ts) (Tuple xs) -> Tuple $ zipWith (poly defs) ts xs
  (Data d ts) (Ctr c x) ->
    case List.find (\ct -> ct.name == c) (getConstructors d ts defs) of
      Nothing -> error . show $ "Datatype" <+> pretty d
        <+> "does not have a constructor" <+> pretty c <> "."
      Just ct -> Ctr c (poly defs ct.field x)
  (Base _) (Lit x) -> Lit x
  t x -> error . show $
    pretty (void x) <+> "does not have type" <+> pretty t <> "."

computePositions :: [Datatype] -> Mono -> Term -> Expr (Position, Term)
computePositions types t e = flip evalState mempty do
  poly types t e & traverse \(v, x) -> do
    m <- get
    let n = fromMaybe 0 $ Map.lookup v m
    modify $ Map.insert v (n + 1)
    return (Position v n, x)

toContainer :: [Datatype] -> Mono -> Term -> Container
toContainer types t = uncurry Container . extract . computePositions types t

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
