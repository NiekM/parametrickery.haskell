module Prettyprinter.Utils where

import Data.Text
import Data.Set (Set)
import Data.Set qualified as Set
import Prettyprinter

statements :: [Doc ann] -> Doc ann
statements = concatWith \x y -> x <> flatAlt line "; " <> y

parensIf :: Bool -> Doc ann -> Doc ann
parensIf p = if p then parens else id

newtype PrettySet a = PrettySet { unPrettySet :: Set a }
  deriving newtype (Eq, Ord, Show)

instance Pretty a => Pretty (PrettySet a) where
  pretty = encloseSep lbrace rbrace ", "
    . fmap pretty
    . Set.toList
    . unPrettySet

-- Used for pretty printing things with a name.
data Named a = Named Text a

prettyNamed :: Pretty (Named a) => Text -> a -> Doc ann
prettyNamed name = pretty . Named name

-- Used for pretty printing things with precedence.
data Prec a = Prec Int a

prettyPrec :: Pretty (Prec a) => Int -> a -> Doc ann
prettyPrec n = pretty . Prec n

prettyMinPrec :: Pretty (Prec a) => a -> Doc ann
prettyMinPrec = prettyPrec minBound

prettyMaxPrec :: Pretty (Prec a) => a -> Doc ann
prettyMaxPrec = prettyPrec maxBound
