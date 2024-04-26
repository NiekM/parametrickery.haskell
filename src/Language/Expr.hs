module Language.Expr where

import Base

import Prettyprinter.Utils

data Lit = MkInt Int | MkBool Bool
  deriving stock (Eq, Ord, Show)

data Expr h where
  Unit :: Expr h
  Pair :: Expr h -> Expr h -> Expr h
  Inl  :: Expr h -> Expr h
  Inr  :: Expr h -> Expr h
  MkList :: [Expr h] -> Expr h
  Lit  :: Lit -> Expr h
  Hole :: h -> Expr h
  deriving stock (Eq, Ord, Show)

mapHole :: (a -> b) -> Expr a -> Expr b
mapHole f = \case
  Unit -> Unit
  Pair x y -> Pair (mapHole f x) (mapHole f y)
  Inl x -> Inl (mapHole f x)
  Inr y -> Inr (mapHole f y)
  MkList xs -> MkList (mapHole f <$> xs)
  Lit l -> Lit l
  Hole v -> Hole (f v)

-- A monomorphic input-output example according to some function signature. We
-- do not have to give a specific type instantiation, because we may make the
-- type more or less abstract. In other words, it is not up to the example to
-- decide which type abstraction we pick.
data Example = Example
  { ins :: [Expr Void]
  , out :: Expr Void
  } deriving stock (Eq, Ord, Show)

------ Pretty ------

instance Pretty Lit where
  pretty = viaShow

instance Pretty h => Pretty (Expr h) where
  pretty = prettyExpr 0

prettyExpr :: Pretty h => Int -> Expr h -> Doc ann
prettyExpr p = \case
  Unit      -> "-"
  Pair x y  -> parensIf 2 p (prettyExpr 2 x <+> "," <+> prettyExpr 2 y)
  Inl x     -> parensIf 2 p ("inl" <+> prettyExpr 3 x)
  Inr y     -> parensIf 2 p ("inr" <+> prettyExpr 3 y)
  MkList xs -> list $ map (prettyExpr 0) xs
  Lit l     -> case l of
    MkInt  n -> pretty n
    MkBool b -> pretty b
  Hole v -> pretty v

instance Pretty Example where
  pretty (Example ins out) =
    sep (map (prettyExpr 3) ins) <+> "->" <+> pretty out
