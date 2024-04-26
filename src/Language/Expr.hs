module Language.Expr where

import Base

import Prettyprinter.Utils

data Lit = MkInt Int | MkNat Nat | MkBool Bool | MkText Text
  deriving stock (Eq, Ord, Show)

data Expr where
  Unit :: Expr
  Pair :: Expr -> Expr -> Expr
  Inl  :: Expr -> Expr
  Inr  :: Expr -> Expr
  MkList :: [Expr] -> Expr
  Lit  :: Lit -> Expr
  deriving stock (Eq, Ord, Show)

-- A monomorphic input-output example according to some function signature. We
-- do not have to give a specific type instantiation, because we may make the
-- type more or less abstract. In other words, it is not up to the example to
-- decide which type abstraction we pick.
data Example = Example
  { ins :: [Expr]
  , out :: Expr
  } deriving stock (Eq, Ord, Show)

------ Pretty ------

instance Pretty Lit where
  pretty = viaShow

instance Pretty Expr where
  pretty = prettyExpr 0

prettyExpr :: Int -> Expr -> Doc ann
prettyExpr p = \case
  Unit      -> "-"
  Pair x y  -> parensIf 2 p (prettyExpr 2 x <+> "," <+> prettyExpr 2 y)
  Inl x     -> parensIf 2 p ("inl" <+> prettyExpr 3 x)
  Inr y     -> parensIf 2 p ("inr" <+> prettyExpr 3 y)
  MkList xs -> list $ map (prettyExpr 0) xs
  Lit l     -> case l of
    MkInt  n -> pretty n
    MkNat  n -> pretty n
    MkBool b -> pretty b
    -- HACK: this does not actually print the quotation marks, which is useful
    -- for printing expressions with variables in them, but a bit of a hack.
    MkText s -> pretty s

instance Pretty Example where
  pretty (Example ins out) =
    sep (map (prettyExpr 3) ins) <+> "->" <+> pretty out
