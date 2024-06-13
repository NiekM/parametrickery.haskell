module Language.Type where

import Base

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

-- Type classes
data Class = None | Eq | Ord
  deriving stock (Eq, Ord, Show)

data Signature = Signature
  { vars :: [(Text, Class)]
  , ctxt :: [(Text, Mono)]
  , goal :: Mono
  } deriving stock (Eq, Ord, Show)

------ Pretty ------

instance Pretty Base where
  pretty = viaShow

instance Pretty Class where
  pretty = viaShow

instance Pretty Mono where
  pretty = prettyMinPrec

instance Pretty (Prec Mono) where
  pretty (Prec p m) = case m of
    Free v  -> pretty v
    Top     -> "1"
    Tup t u -> parensIf (p > 2) $ sep [prettyPrec 3 t, "*", prettyPrec 2 u]
    Sum t u -> parensIf (p > 1) $ sep [prettyPrec 2 t, "+", prettyPrec 1 u]
    List t  -> brackets $ pretty t
    Base b  -> pretty b

instance Pretty Signature where
  pretty (Signature vars ctxt goal) = cat
    [ quantifiers (fst <$> vars)
    , constraints (filter ((/= None) . snd) vars)
    , arguments ctxt
    , pretty goal
    ] where
      quantifiers [] = ""
      quantifiers xs = sep ("forall" : map pretty xs) <> ". "
      constraints [] = ""
      constraints xs =
        tupled (xs <&> \(x, c) -> pretty c <+> pretty x) <+> "=> "
      arguments [] = ""
      arguments xs = encloseSep lbrace rbrace ", "
        (xs <&> \(x, t) -> pretty x <+> ":" <+> pretty t) <+> "-> "

instance Pretty (Named Signature) where
  pretty (Named name sig) = sep [pretty name, ":", pretty sig]
