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
  projections :: Project a => a -> Maybe [a]
  projections x = sequence . takeWhile isJust $ (`project` x) <$> [0..]

  project :: Nat -> a -> Maybe a
  project i x = projections x >>= (List.!? fromIntegral i)

instance Project (Expr h) where
  projections = \case
    Tuple xs -> Just xs
    _ -> Nothing

instance Project Mono where
  projections = \case
    Product ts -> Just ts
    _ -> Nothing

instance Project Example where
  projections (Example ins out) = fmap (Example ins) <$> projections out

instance Project Signature where
  projections sig = do
    ts <- projections sig.goal
    return $ ts <&> \t -> sig { goal = t }

instance Project Problem where
  projections prob = do
    ss <- projections prob.signature
    bs <- forM prob.bindings projections
    return $ zipWith Declaration ss (List.transpose bs)
