module Pretty where

import Base
import Text.Show

class Pretty f where
  pretty :: Show a => Int -> f a -> ShowS

  default pretty :: (Show1 f, Show a) => Int -> f a -> ShowS
  pretty = showsPrec

prettyList :: (Pretty f, Show a) => [f a] -> ShowS
prettyList = showListWith $ pretty 0

instance Pretty []
instance Pretty Maybe

instance Pretty Identity where
  pretty n = showsPrec n . runIdentity

instance Show k => Pretty (Const k) where
  pretty n = showsPrec n . getConst

instance (Pretty f, Pretty g) => Pretty (Product f g) where
  pretty n (Pair x y) =
    liftShowsPrec2 pretty prettyList pretty prettyList n (x, y)
