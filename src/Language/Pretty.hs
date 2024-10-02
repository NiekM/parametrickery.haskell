{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Pretty where

import Data.Set qualified as Set
import Data.Map qualified as Map

import Prettyprinter

import Base

import Data.Named
import Data.Map.Multi qualified as Multi

import Language.Type
import Language.Expr
import Language.Container
import Language.Container.Morphism
import Language.Container.Relation
import Language.Coverage
import Language.Problem
import Language.Relevance

statements :: [Doc ann] -> Doc ann
statements = concatWith \x y -> x <> flatAlt line "; " <> y

parensIf :: Bool -> Doc ann -> Doc ann
parensIf p = if p then parens else id

braced :: [Doc ann] -> Doc ann
braced = encloseSep lbrace rbrace ", "

-- Used for pretty printing with precedence.
data Prec a = Prec Int a

prettyPrec :: Pretty (Prec a) => Int -> a -> Doc ann
prettyPrec n = pretty . Prec n

prettyMinPrec :: Pretty (Prec a) => a -> Doc ann
prettyMinPrec = prettyPrec minBound

prettyMaxPrec :: Pretty (Prec a) => a -> Doc ann
prettyMaxPrec = prettyPrec maxBound

instance Pretty Lit where
  pretty = \case
    MkInt n -> pretty n

instance Pretty (Hole Void) where
  pretty (MkHole h) = absurd h

instance Pretty (Hole ()) where
  pretty = const "_"

instance Pretty (Hole Text) where
  pretty (MkHole h) = braces $ pretty h

instance Pretty (Hole h) => Pretty (Expr h) where
  pretty = prettyMinPrec

instance Pretty (Hole h) => Pretty (Prec (Expr h)) where
  pretty (Prec p e) = case e of
    Tuple xs -> tupled $ map pretty xs
    List xs -> pretty xs
    Ctr c Unit -> pretty c
    Ctr c x -> parensIf (p > 2) $ pretty c <+> prettyPrec 3 x
    Lit l -> pretty l
    Hole v -> pretty v

instance Pretty Example where
  pretty (Example [] out) = pretty out
  pretty (Example ins out) =
    sep (map prettyMaxPrec ins) <+> "->" <+> pretty out

instance Pretty (Named Example) where
  pretty (Named name (Example ins out)) =
    sep (pretty name : map prettyMaxPrec ins ++ ["=", pretty out])

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
      arguments xs = braced (map pretty xs) <+> "-> "

instance Pretty (Named Signature) where
  pretty (Named name sig) = pretty name <+> ":" <+> pretty sig

instance Pretty Problem where
  pretty = prettyNamed "_"

instance Pretty (Named Problem) where
  pretty (Named name (Problem sig exs)) = statements $
    prettyNamed name sig : map (prettyNamed name) exs

instance Pretty Arg where
  pretty (Arg t es) = pretty t <+> "=" <+> braced (map pretty es)

instance Pretty (Named Arg) where
  pretty (Named name (Arg t es)) = prettyNamed name t
    <+> "=" <+> braced (map pretty es)

instance Pretty Args where
  pretty (Args inputs output) = statements
    [ statements $ map pretty inputs
    , "->" <+> pretty output
    ]

instance Pretty Relevance where
  pretty (Relevance rel) = pretty rel

instance Pretty Position where
  pretty (Position a n) = pretty a <> pretty n

instance Pretty (Hole Position) where
  pretty (MkHole p) = pretty p

instance Pretty Container where
  pretty (Container s p) = pretty s <+> braced xs
    where
      xs = Map.assocs p <&> \(i, x) -> pretty i <+> "=" <+> pretty x

instance Pretty (Hole (Set Position)) where
  pretty (MkHole ps) = case Set.toList ps of
    [x] -> pretty x
    xs  -> braced $ map pretty xs

instance Pretty Pattern where
  pretty patt
    | null relations = inputs
    | otherwise = inputs <+> "|" <+>
      concatWith (surround ", ") (pretty <$> relations)
    where
      inputs = sep (map prettyMaxPrec patt.shapes)
      relations = filter relevant patt.relations

instance Pretty Rule where
  pretty Rule { input, output, origins }
    | null input.shapes = pretty output
    | otherwise = pretty input <+> "->" <+> out
    where
      out = pretty $ fmap (`Multi.lookup` origins) output

instance Pretty (Named Rule) where
  pretty (Named name Rule { input, output, origins })
    | null input.shapes = pretty name <+> "=" <+> out
    | otherwise = pretty name <+> pretty input <+> "=" <+> out
    where
      out = pretty $ fmap (`Multi.lookup` origins) output

instance Pretty Conflict where
  pretty = \case
    ArgumentMismatch ts es -> "ArgumentMismatch!" <+> indent 2
      (vcat [pretty ts, pretty es])
    ShapeConflict xs -> "ShapeConflict!" <+> indent 2 (pretty xs)
    MagicOutput x -> "MagicOutput!" <+> indent 2 (pretty x)
    PositionConflict xs -> "PositionConflict!" <+> indent 2 (pretty xs)

instance Pretty Coverage where
  pretty = \case
    Total -> "Total"
    Partial -> "Partial"
    Missing c -> vcat $ "Partial, missing cases:"
      : map pretty (Set.toList c)

eqClass :: Pretty a => Set a -> Doc ann
eqClass s = case Set.toList s of
  [x] -> pretty x
  xs  -> concatWith (surround " == ") $ map pretty xs

instance Pretty Relation where
  pretty = \case
    RelEq  eq  -> concatWith (surround " /= ") . fmap eqClass $ Set.toList eq
    RelOrd ord -> concatWith (surround " < " ) $ fmap eqClass ord
