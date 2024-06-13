module Language.Expr where

import Data.Map.Strict qualified as Map

import Base

import Prettyprinter.Utils

data Lit = MkInt Int | MkBool Bool
  deriving stock (Eq, Ord, Show)

-- TODO: we could replace Unit and Pair with an n-ary tuple [Expr h];
--       and remove Inl and Inr in favor of some Ctr :: Text -> Expr h -> Expr h
data Expr h where
  Unit :: Expr h
  Pair :: Expr h -> Expr h -> Expr h
  Inl  :: Expr h -> Expr h
  Inr  :: Expr h -> Expr h
  Lst  :: [Expr h] -> Expr h
  Lit  :: Lit -> Expr h
  Hole :: h -> Expr h
  deriving stock (Eq, Ord, Show)
  deriving stock (Functor, Foldable, Traversable)

type Term = Expr Void

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

match :: Ord a => Expr a -> Expr b -> Maybe (Map a (Expr b))
match = \cases
  Unit       Unit       -> Just mempty
  (Pair x y) (Pair a b) -> Map.union <$> match x a <*> match y b
  (Inl x)    (Inl a)    -> match x a
  (Inr y)    (Inr b)    -> match y b
  (Lst xs)   (Lst as) | length xs == length as ->
    Map.unions <$> zipWithM match xs as
  (Lit l)    (Lit m)  | l == m -> Just mempty
  (Hole h)   e          -> Just $ Map.singleton h e
  _ _ -> Nothing

-- A monomorphic input-output example according to some function signature. We
-- do not have to give a specific type instantiation, because we may make the
-- type more or less abstract. In other words, it is not up to the example to
-- decide which type abstraction we pick.
data Example = Example
  { inputs :: [Term]
  , output :: Term
  } deriving stock (Eq, Ord, Show)

------ Pretty ------

instance Pretty Lit where
  pretty = \case
    MkInt  n -> pretty n
    MkBool b -> pretty b

instance Pretty h => Pretty (Expr h) where
  pretty = prettyMinPrec

instance Pretty h => Pretty (Prec (Expr h)) where
  pretty (Prec p e) = case e of
    Unit     -> "-"
    Pair x y -> parens (prettyPrec 2 x <> "," <+> prettyPrec 2 y)
    Inl x    -> parensIf (p > 2) ("inl" <+> prettyPrec 3 x)
    Inr y    -> parensIf (p > 2) ("inr" <+> prettyPrec 3 y)
    Lst xs   -> list $ map (prettyPrec 0) xs
    Lit l    -> pretty l
    Hole v   -> pretty v

instance Pretty Example where
  pretty (Example [] out) = pretty out
  pretty (Example ins out) =
    sep (map prettyMaxPrec ins) <+> "->" <+> pretty out

instance Pretty (Named Example) where
  pretty (Named name (Example ins out)) =
    sep (pretty name : map prettyMaxPrec ins ++ ["=", pretty out])
