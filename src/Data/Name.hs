module Data.Name
  ( Name(Name)
  , Named(..)
  , fromString
  , prettyNamed
  ) where

import Data.String

import Data.Text
import Prettyprinter

newtype Name = Name { getName :: Text }
  deriving stock (Eq, Ord, Show)
  deriving newtype (Semigroup, Monoid, IsString, Pretty)

data Named a = Named { name :: Name, value :: a }
  deriving stock (Eq, Ord, Show)
  deriving stock (Functor, Foldable, Traversable)

-- It is a common pattern to print something with a name. In these cases
-- 'Named' can be used as a wrapper before calling 'pretty'.
prettyNamed :: Pretty (Named a) => Name -> a -> Doc ann
prettyNamed name = pretty . Named name
