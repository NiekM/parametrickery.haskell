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
  Lst  :: [Expr h] -> Expr h
  Lit  :: Lit -> Expr h
  Hole :: h -> Expr h
  deriving stock (Eq, Ord, Show)

instance Functor Expr where
  fmap :: (a -> b) -> Expr a -> Expr b
  fmap f = \case
    Unit     -> Unit
    Pair x y -> Pair (fmap f x) (fmap f y)
    Inl x    -> Inl (fmap f x)
    Inr y    -> Inr (fmap f y)
    Lst xs   -> Lst (fmap f <$> xs)
    Lit l    -> Lit l
    Hole v   -> Hole (f v)

instance Applicative Expr where
  pure :: a -> Expr a
  pure = Hole

  liftA2 :: (a -> b -> c) -> Expr a -> Expr b -> Expr c
  liftA2 f x y = x >>= \a -> y >>= \b -> pure $ f a b

instance Monad Expr where
  (>>=) :: Expr a -> (a -> Expr b) -> Expr b
  x >>= f = accept $ fmap f x

-- Accept the hole fillings (i.e. join)
accept :: Expr (Expr h) -> Expr h
accept = \case
  Unit     -> Unit
  Pair x y -> Pair (accept x) (accept y)
  Inl x    -> Inl (accept x)
  Inr y    -> Inr (accept y)
  Lst xs   -> Lst (accept <$> xs)
  Lit l    -> Lit l
  Hole e   -> e

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
  pretty = \case
    MkInt  n -> pretty n
    MkBool b -> pretty b

instance Pretty h => Pretty (Expr h) where
  pretty = prettyExpr 0

prettyExpr :: Pretty h => Int -> Expr h -> Doc ann
prettyExpr p = \case
  Unit     -> "-"
  Pair x y -> parensIf 2 p (prettyExpr 2 x <+> "," <+> prettyExpr 2 y)
  Inl x    -> parensIf 2 p ("inl" <+> prettyExpr 3 x)
  Inr y    -> parensIf 2 p ("inr" <+> prettyExpr 3 y)
  Lst xs   -> list $ map (prettyExpr 0) xs
  Lit l    -> pretty l
  Hole v   -> pretty v

instance Pretty Example where
  pretty (Example ins out) =
    sep (map (prettyExpr 3) ins) <+> "->" <+> pretty out
