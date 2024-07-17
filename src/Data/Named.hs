module Data.Named where

import Data.Text
import Prettyprinter

data Named a = Named { name :: Text, value :: a }
  deriving stock (Eq, Ord, Show)
  deriving stock (Functor, Foldable, Traversable)

-- It is a common pattern to print something with a name. In these cases
-- 'Named' can be used as a wrapper before calling 'pretty'.
prettyNamed :: Pretty (Named a) => Text -> a -> Doc ann
prettyNamed name = pretty . Named name
