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

data Base = Int | Nat | Bool | Text
  deriving stock (Eq, Ord, Show)

-- Type classes.
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

-- TODO: should we create a class PrettyPrec?
instance Pretty Mono where
  pretty = prettyMono 0

prettyMono :: Int -> Mono -> Doc ann
prettyMono p = \case
  Free v -> pretty v
  Top -> "1"
  Tup t u -> parensIf 2 p (prettyMono 3 t <+> "*" <+> prettyMono 2 u)
  Sum t u -> parensIf 1 p (prettyMono 2 t <+> "+" <+> prettyMono 1 u)
  List t -> brackets $ pretty t
  Base b -> pretty b

instance Pretty Signature where
  pretty (Signature vars ctxt goal) = cat
    [ quantify (fst <$> vars)
    , constraints (filter ((/= None) . snd) vars)
    , arguments ctxt
    , pretty goal
    ] where
      quantify [] = ""
      quantify xs = sep ("forall" : map pretty xs) <> ". "
      constraints [] = ""
      constraints xs =
        tupled (xs <&> \(x, c) -> pretty c <+> pretty x) <+> "=> "
      arguments [] = ""
      arguments xs = encloseSep lbrace rbrace ", "
        (xs <&> \(x, t) -> pretty x <+> ":" <+> pretty t) <+> "-> "
