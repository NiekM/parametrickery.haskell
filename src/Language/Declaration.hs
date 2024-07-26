{-# LANGUAGE UndecidableInstances #-}

module Language.Declaration where

import Prettyprinter.Utils
import Base
import Data.Named
import Language.Expr
import Language.Type

-- | A declaration consists of a signature with some bindings.
data Declaration binding = Declaration
  { signature :: Signature
  , bindings  :: [binding]
  } deriving stock (Eq, Ord, Show)

type Problem = Declaration Example

instance Pretty (Named binding) => Pretty (Declaration binding) where
  pretty = prettyNamed "_"
 
instance Pretty (Named binding) => Pretty (Named (Declaration binding)) where
  pretty (Named name (Declaration sig exs)) =
    statements (prettyNamed name sig : map (prettyNamed name) exs)
