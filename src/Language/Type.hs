module Language.Type where

import Data.List qualified as List
import Data.Map qualified as Map

import Base
import Data.Named

-- We could try to design our framework to be generic over the types and
-- expressions, by creating some type class that provides e.g. a lens to the
-- polymorphic variables. The specific datatypes used can decide how
-- deep/shallow and typed/untyped their embedding is, as long as they provide
-- the right interface.
data Mono where
  Free :: Text -> Mono
  Product :: [Mono] -> Mono
  Data :: Text -> [Mono] -> Mono
  Base :: Base -> Mono
  deriving stock (Eq, Ord, Show)

pattern Top :: Mono
pattern Top = Product []

instantiate :: Map Text Mono -> Mono -> Mono
instantiate m = \case
  Free a | Just t <- Map.lookup a m -> t
  Free a -> Free a
  Product ts -> Product (instantiate m <$> ts)
  Data d ts -> Data d (instantiate m <$> ts)
  Base b -> Base b

-- Base types
data Base = Int
  deriving stock (Eq, Ord, Show)

data Constructor = Constructor
  { name  :: Text
  , field :: Mono
  } deriving stock (Eq, Ord, Show)

data Datatype = Datatype
  { name :: Text
  , arguments :: [Text]
  , constructors :: [Constructor]
  } deriving stock (Eq, Ord, Show)

newtype Context = Context
  { datatypes :: [Datatype]
  } deriving stock (Eq, Ord, Show)

getConstructors :: Text -> [Mono] -> Context -> [Constructor]
getConstructors name ts ctx =
  case List.find (\d -> d.name == name) ctx.datatypes of
    Nothing -> error "Unknown datatype"
    Just datatype ->
      let mapping = Map.fromList $ zip datatype.arguments ts
      in datatype.constructors <&> \(Constructor c t) ->
        Constructor c (instantiate mapping t)

-- TODO: have some sort of Prelude file
datatypes :: Context
datatypes = Context
  [ Datatype
    { name = "Bool"
    , arguments = []
    , constructors =
      [ Constructor { name = "False", field = Top }
      , Constructor { name = "True" , field = Top }
      ]
    }
  , Datatype
    { name = "Maybe"
    , arguments = ["a"]
    , constructors =
      [ Constructor { name = "Nothing", field = Top }
      , Constructor { name = "Just"   , field = Free "a" }
      ]
    }
  , Datatype
    { name = "Either"
    , arguments = ["a", "b"]
    , constructors =
      [ Constructor { name = "Left" , field = Free "a" }
      , Constructor { name = "Right", field = Free "b" }
      ]
    }
  , Datatype
    { name = "List"
    , arguments = ["a"]
    , constructors =
      [ Constructor { name = "Nil", field = Top }
      , Constructor
        { name = "Cons"
        , field = Product [Free "a", Data "List" [Free "a"]]
        }
      ]
    }
  , Datatype
    { name = "Tree"
    , arguments = ["a", "b"]
    , constructors =
      [ Constructor { name = "Leaf", field = Free "b" }
      , Constructor
        { name = "Node"
        , field = Product
          -- TODO: perhaps we can do recursion by using e.g. `Free "rec"`
          [ Data "Tree" [Free "a", Free "b"]
          , Free "a"
          , Data "Tree" [Free "a", Free "b"]
          ]
        }
      ]
    }
  ]

data Constraint = Eq Text | Ord Text
  deriving stock (Eq, Ord, Show)

data Signature = Signature
  { constraints :: [Constraint]
  , inputs      :: [Named Mono]
  , output      :: Mono
  } deriving stock (Eq, Ord, Show)
