{-# LANGUAGE UndecidableInstances #-}

module Language.Declaration where

import Data.List qualified as List

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

class Project a where
  projections :: Project a => a -> [a]

instance Project (Expr h) where
  projections = \case
    Tuple xs -> xs
    x -> [x]

instance Project Mono where
  projections = \case
    Product ts -> ts
    t -> [t]

instance Project Example where
  projections (Example ins out) = Example ins <$> projections out

instance Project Signature where
  projections sig = projections sig.goal <&> \t -> sig { goal = t }

instance Project Problem where
  projections prob = zipWith Declaration ss bs
    where
      ss = projections prob.signature
      bs = List.transpose $ map projections prob.bindings
