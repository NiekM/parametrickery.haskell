module Language.Type where

import Data.Functor.Compose
import Data.Monoid (Any(..))
import Data.Map qualified as Map
import Data.Set qualified as Set

import Base

-- We could try to design our framework to be generic over the types and
-- expressions, by creating some type class that provides e.g. a lens to the
-- polymorphic variables. The specific datatypes used can decide how
-- deep/shallow and typed/untyped their embedding is, as long as they provide
-- the right interface.
data Mono where
  Free :: Name -> Mono
  Product :: [Mono] -> Mono
  Data :: Name -> [Mono] -> Mono
  Base :: Base -> Mono
  deriving stock (Eq, Ord, Show)

pattern Top :: Mono
pattern Top = Product []

instance Project Mono where
  projections = \case
    Product ts -> ts
    t -> [t]

instantiate :: Map Name Mono -> Mono -> Mono
instantiate m = \case
  Free a | Just t <- Map.lookup a m -> t
  Free a -> Free a
  Product ts -> Product (instantiate m <$> ts)
  Data d ts -> Data d (instantiate m <$> ts)
  Base b -> Base b

-- Base types
data Base = Int
  deriving stock (Eq, Ord, Show)

getFree :: Mono -> Set Name
getFree = \case
  Free a -> Set.singleton a
  Product ts -> foldMap getFree ts
  Data _ ts -> foldMap getFree ts
  Base _ -> Set.empty

type Constructor = Named Mono

data DataDef = DataDef
  { arguments :: [Name]
  , constructors :: [Constructor]
  } deriving stock (Eq, Ord, Show)

base :: Named DataDef -> Maybe (Named DataDef)
base (Named name def)
  | recursive = Just $ Named (name <> "F") basedef
  | otherwise = Nothing
  where
    basedef = DataDef (def.arguments ++ ["r"]) cs

    (Any recursive, Compose cs) = traverse locate (Compose def.constructors)

    locate :: Mono -> (Any, Mono)
    locate = \case
      t | t == Data name (Free <$> def.arguments) -> (Any True, Free "r")
      Product ts -> Product <$> traverse locate ts
      Data d ts -> Data d <$> traverse locate ts
      t -> (Any False, t)

newtype Context = Context
  { datatypes :: [Named DataDef]
  } deriving stock (Eq, Ord, Show)

getConstructors :: Name -> [Mono] -> Context -> [Constructor]
getConstructors name ts ctx =
  case find name ctx.datatypes of
    Nothing -> error $ "Unknown datatype " <> show name
    Just datatype ->
      let mapping = Map.fromList $ zip datatype.arguments ts
      in datatype.constructors <&> \(Named c t) ->
        Named c (instantiate mapping t)

data Constraint = Eq Name | Ord Name
  deriving stock (Eq, Ord, Show)

data Signature = Signature
  { constraints :: [Constraint]
  , inputs      :: [Named Mono]
  , output      :: Mono
  } deriving stock (Eq, Ord, Show)

instance Project Signature where
  projections sig = do
    output <- projections sig.output
    return (sig { output } :: Signature)
