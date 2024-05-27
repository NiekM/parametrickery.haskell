module Pretty where

import Base
import Text.Show

import Data.Dup

-- TODO: use prettyprinter???
class Pretty f where
  pretty :: Show a => Int -> f a -> ShowS

  default pretty :: (Show1 f, Show a) => Int -> f a -> ShowS
  pretty = showsPrec

newtype PrettyShow f a = PrettyShow (f a)

instance (Pretty f, Show a) => Show (PrettyShow f a) where
  showsPrec n (PrettyShow x) = pretty n x

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

instance (Pretty f, Pretty g) => Pretty (Sum f g) where
  pretty n = \case
    InL x -> liftShowsPrec2 pretty prettyList undefined undefined n (Left  x)
    InR y -> liftShowsPrec2 undefined undefined pretty prettyList n (Right y)

instance (Functor f, Pretty f, Pretty g) => Pretty (Compose f g) where
  pretty n (Compose x) = pretty n (PrettyShow <$> x)

instance Pretty Dup where
  pretty n (Dup (x, y)) =
    liftShowsPrec2 showsPrec showList showsPrec showList n (x, y)
