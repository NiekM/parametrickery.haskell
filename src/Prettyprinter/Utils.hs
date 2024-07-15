module Prettyprinter.Utils where

import Prettyprinter

statements :: [Doc ann] -> Doc ann
statements = concatWith \x y -> x <> flatAlt line "; " <> y

parensIf :: Bool -> Doc ann -> Doc ann
parensIf p = if p then parens else id
