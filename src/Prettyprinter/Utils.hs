module Prettyprinter.Utils where

import Prettyprinter

statements :: [Doc ann] -> Doc ann
statements = concatWith \x y -> x <> flatAlt line "; " <> y

parensIf :: Int -> Int -> Doc ann -> Doc ann
parensIf n p = if n < p then parens else id
