module Language.Type where

import Data.Map qualified as Map

import Base
import Data.Named
import Prettyprinter.Utils

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

-- TODO: have some sort of Prelude file
datatypes :: [Datatype]
datatypes =
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
  , context     :: [Named Mono]
  , goal        :: Mono
  } deriving stock (Eq, Ord, Show)

------ Pretty ------

instance Pretty Base where
  pretty = viaShow

instance Pretty Constraint where
  pretty = \case
    Eq  a -> "Eq"  <+> pretty a
    Ord a -> "Ord" <+> pretty a

instance Pretty Mono where
  pretty = prettyMinPrec

instance Pretty (Prec Mono) where
  pretty (Prec p t) = case t of
    Free v -> pretty v
    Product ts -> tupled $ map pretty ts
    Data d [] -> pretty d
    Data d ts -> parensIf (p > 2) $ pretty d <+> sep (prettyPrec 3 <$> ts)
    Base b -> pretty b

instance Pretty (Named Mono) where
  pretty (Named x t) = pretty x <+> ":" <+> pretty t

instance Pretty Signature where
  pretty Signature { constraints, context, goal } = cat
    [ constrs constraints
    , arguments context
    , pretty goal
    ] where
      constrs [] = ""
      constrs [x] = pretty x <+> "=> "
      constrs xs = tupled (map pretty xs) <+> "=> "
      arguments [] = ""
      arguments xs = encloseSep lbrace rbrace ", " (map pretty xs) <+> "-> "

instance Pretty (Named Signature) where
  pretty (Named name sig) = pretty name <+> ":" <+> pretty sig
