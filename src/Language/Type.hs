module Language.Type where

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
  Top  :: Mono
  Tup  :: Mono -> Mono -> Mono
  Sum  :: Mono -> Mono -> Mono
  List :: Mono -> Mono
  Base :: Base -> Mono
  deriving stock (Eq, Ord, Show)

-- Base types
data Base = Int | Bool
  deriving stock (Eq, Ord, Show)

data Constraint = Eq Text | Ord Text
  deriving stock (Eq, Ord, Show)

data Signature = Signature
  { vars        :: [Text]
  , constraints :: [Constraint]
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

instance Pretty (Named Mono) where
  pretty (Named x t) = pretty x <+> ":" <+> pretty t

instance Pretty (Prec Mono) where
  pretty (Prec p m) = case m of
    Free v  -> pretty v
    Top     -> "1"
    Tup t u -> parensIf (p > 2) $ sep [prettyPrec 3 t, "*", prettyPrec 2 u]
    Sum t u -> parensIf (p > 1) $ sep [prettyPrec 2 t, "+", prettyPrec 1 u]
    List t  -> brackets $ pretty t
    Base b  -> pretty b

instance Pretty Signature where
  pretty Signature { vars, constraints, context, goal } = cat
    [ quantifiers vars
    , constrs constraints
    , arguments context
    , pretty goal
    ] where
      quantifiers [] = ""
      quantifiers xs = sep ("forall" : map pretty xs) <> ". "
      constrs [] = ""
      constrs [x] = pretty x <+> "=> "
      constrs xs = tupled (map pretty xs) <+> "=> "
      arguments [] = ""
      arguments xs = encloseSep lbrace rbrace ", " (map pretty xs) <+> "-> "

instance Pretty (Named Signature) where
  pretty (Named name sig) = sep [pretty name, ":", pretty sig]
