module Language.Type where

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
  Sum :: [Mono] -> Mono
  List :: Mono -> Mono
  Base :: Base -> Mono
  deriving stock (Eq, Ord, Show)

-- Base types
data Base = Int | Bool
  deriving stock (Eq, Ord, Show)

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
  pretty = \case
    Free v  -> pretty v
    Product ts -> tupled $ map pretty ts
    Sum ts -> encloseSep lparen rparen " | " $ map pretty ts
    List t  -> brackets $ pretty t
    Base b  -> pretty b

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
