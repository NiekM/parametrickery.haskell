module Language.Type where

import Data.List qualified as List
import Data.Map qualified as Map

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

type Constructor = Named Mono

data Datatype = Datatype
  { name :: Name
  , arguments :: [Name]
  , constructors :: [Constructor]
  } deriving stock (Eq, Ord, Show)

newtype Context = Context
  { datatypes :: [Datatype]
  } deriving stock (Eq, Ord, Show)

getConstructors :: Name -> [Mono] -> Context -> [Constructor]
getConstructors name ts ctx =
  case List.find (\d -> d.name == name) ctx.datatypes of
    Nothing -> error "Unknown datatype"
    Just datatype ->
      let mapping = Map.fromList $ zip datatype.arguments ts
      in datatype.constructors <&> \(Named c t) ->
        Named c (instantiate mapping t)

-- TODO: have some sort of Prelude file
datatypes :: Context
datatypes = Context
  [ Datatype
    { name = "Bool"
    , arguments = []
    , constructors =
      [ Named "False" Top
      , Named "True"  Top
      ]
    }
  , Datatype
    { name = "Nat"
    , arguments = []
    , constructors =
      [ Named "Zero" Top
      , Named "Succ" (Data "Nat" [])
      ]
    }
  , Datatype
    { name = "Maybe"
    , arguments = ["a"]
    , constructors =
      [ Named "Nothing" Top
      , Named "Just"    (Free "a")
      ]
    }
  , Datatype
    { name = "Either"
    , arguments = ["a", "b"]
    , constructors =
      [ Named "Left"  (Free "a")
      , Named "Right" (Free "b")
      ]
    }
  , Datatype
    { name = "List"
    , arguments = ["a"]
    , constructors =
      [ Named "Nil"  Top
      , Named "Cons" (Product [Free "a", Data "List" [Free "a"]])
      ]
    }
  , Datatype
    { name = "Tree"
    , arguments = ["a", "b"]
    , constructors =
      [ Named "Leaf" (Free "b")
      , Named "Node" $ Product
        -- TODO: perhaps we can do recursion by using e.g. `Free "rec"`
        [ Data "Tree" [Free "a", Free "b"]
        , Free "a"
        , Data "Tree" [Free "a", Free "b"]
        ]
      ]
    }
  ]

data Constraint = Eq Name | Ord Name
  deriving stock (Eq, Ord, Show)

data Signature = Signature
  { constraints :: [Constraint]
  , inputs      :: [Named Mono]
  , output      :: Mono
  } deriving stock (Eq, Ord, Show)
