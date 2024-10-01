{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Language.Declaration where

import Data.List qualified as List
import Data.Set qualified as Set

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

data Arg = Arg
  { mono :: Mono
  , terms :: [Term]
  } deriving (Eq, Ord, Show)

instance Pretty Arg where
  pretty (Arg t es) = pretty t
    <+> "=" <+> encloseSep lbrace rbrace ", " (map pretty es)

instance Pretty (Named Arg) where
  pretty (Named name (Arg t es)) = prettyNamed name t
    <+> "=" <+> encloseSep lbrace rbrace ", " (map pretty es)

data Args = Args
  { constraints :: [Constraint]
  , inputs :: [Named Arg]
  , output :: Arg
  } deriving stock (Eq, Ord, Show)

instance Pretty Args where
  pretty (Args constraints inputs output) = statements $
    constrs constraints ++
    [ statements $ map pretty inputs
    , "->" <+> pretty output
    ] where
      constrs [] = []
      constrs xs = [tupled (map pretty xs)]

-- TODO: define this as an Iso from lens, or remove `constraints` and have it be
-- a Lens
toArgs :: Problem -> Args
toArgs (Declaration signature examples) = Args
  { constraints = signature.constraints
  , inputs = zipWith (fmap . flip Arg) inputs signature.context
  , output = Arg signature.goal outputs
  } where
    (inputs, outputs) = first List.transpose . unzip
      $ examples <&> \ex -> (ex.inputs, ex.output)

fromArgs :: Args -> Problem
fromArgs (Args constraints args (Arg goal outputs)) = Declaration
  { signature = Signature
    { constraints
    , context = args <&> fmap (.mono)
    , goal
    }
  , bindings = zipWith Example (inputs ++ repeat []) outputs
  } where
    inputs = List.transpose $ args <&> \arg -> arg.value.terms

onArgs :: (Args -> Args) -> Problem -> Problem
onArgs f = fromArgs . f . toArgs

restrict :: Set Text -> Args -> Args
restrict ss args =
  args { inputs = filter (\arg -> arg.name `Set.member` ss) args.inputs }

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

instance Project Arg where
  projections = \case
    Arg (Product ts) es -> zipWith Arg ts . List.transpose $ map projections es
    a -> [a]
