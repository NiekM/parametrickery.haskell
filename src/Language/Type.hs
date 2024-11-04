module Language.Type where

import Data.List qualified as List
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
  { name :: Name
  , arguments :: [Name]
  , constructors :: [Constructor]
  } deriving stock (Eq, Ord, Show)

newtype Context = Context
  { datatypes :: [DataDef]
  } deriving stock (Eq, Ord, Show)

getConstructors :: Name -> [Mono] -> Context -> [Constructor]
getConstructors name ts ctx =
  case List.find (\d -> d.name == name) ctx.datatypes of
    Nothing -> error "Unknown datatype"
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
