{-# LANGUAGE UndecidableInstances #-}

module Language.Expr where

import Base
import Data.Named

data Lit = MkInt Int | MkBool Bool
  deriving stock (Eq, Ord, Show)

-- Used for pretty printing
newtype Hole h = MkHole { hole :: h }
  deriving stock (Eq, Ord, Show)
  deriving stock (Functor, Foldable, Traversable)

data Expr h where
  Tuple :: [Expr h] -> Expr h
  Proj :: Nat -> Nat -> Expr h -> Expr h
  Lst  :: [Expr h] -> Expr h
  Lit  :: Lit -> Expr h
  Hole :: Hole h -> Expr h
  deriving stock (Eq, Ord, Show)
  deriving stock (Functor, Foldable, Traversable)

type Term = Expr Void

instance Applicative Expr where
  pure :: a -> Expr a
  pure = Hole . MkHole

  liftA2 :: (a -> b -> c) -> Expr a -> Expr b -> Expr c
  liftA2 f x y = x >>= \a -> y >>= \b -> pure $ f a b

instance Monad Expr where
  (>>=) :: Expr a -> (a -> Expr b) -> Expr b
  x >>= f = accept $ fmap f x

-- Accept the hole fillings (i.e. join)
accept :: Expr (Expr h) -> Expr h
accept = \case
  Tuple xs -> Tuple (map accept xs)
  Proj i n x -> Proj i n (accept x)
  Lst xs -> Lst (map accept xs)
  Lit l -> Lit l
  Hole e -> e.hole

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

instance Pretty (Hole Void) where
  pretty (MkHole h) = absurd h

instance Pretty (Hole ()) where
  pretty = const "_"

instance Pretty (Hole h) => Pretty (Hole (Expr h)) where
  pretty (MkHole h) = braces $ pretty h

instance Pretty (Hole h) => Pretty (Expr h) where
  pretty = \case
    Tuple xs -> tupled $ map pretty xs
    Proj i n x -> encloseSep lparen rparen "|" $
      replicate (fromIntegral i) mempty
      ++ pretty x : replicate (fromIntegral (n - i - 1)) mempty
    Lst xs   -> pretty xs
    Lit l    -> pretty l
    Hole v   -> pretty v

instance Pretty Example where
  pretty (Example [] out) = pretty out
  pretty (Example ins out) =
    sep (map pretty ins) <+> "->" <+> pretty out

instance Pretty (Named Example) where
  pretty (Named name (Example ins out)) =
    sep (pretty name : map pretty ins ++ ["=", pretty out])
