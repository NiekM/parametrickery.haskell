module Prettyprinter.Utils where

import Prettyprinter

statements :: [Doc ann] -> Doc ann
statements = concatWith \x y -> x <> flatAlt line "; " <> y

parensIf :: Bool -> Doc ann -> Doc ann
parensIf p = if p then parens else id

-- Used for pretty printing things with precedence.
data Prec a = Prec Int a

prettyPrec :: Pretty (Prec a) => Int -> a -> Doc ann
prettyPrec n = pretty . Prec n

prettyMinPrec :: Pretty (Prec a) => a -> Doc ann
prettyMinPrec = prettyPrec minBound

prettyMaxPrec :: Pretty (Prec a) => a -> Doc ann
prettyMaxPrec = prettyPrec maxBound
