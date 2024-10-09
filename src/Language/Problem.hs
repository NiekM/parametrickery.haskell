{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Language.Problem where

import Data.List qualified as List
import Data.Set qualified as Set

import Base
import Data.Named
import Language.Expr
import Language.Type

-- | A declaration consists of a signature with some bindings.
data Problem = Problem
  { signature :: Signature
  , examples  :: [Example]
  } deriving stock (Eq, Ord, Show)

data Arg = Arg
  { mono  :: Mono
  , terms :: [Value]
  } deriving stock (Eq, Ord, Show)

data Args = Args
  { inputs :: [Named Arg]
  , output :: Arg
  } deriving stock (Eq, Ord, Show)

-- TODO: define this as an Iso from lens, or remove `constraints` and have it be
-- a Lens
toArgs :: Problem -> Args
toArgs (Problem signature examples) = Args
  { inputs = zipWith (fmap . flip Arg) inputs signature.inputs
  , output = Arg signature.output outputs
  } where
    (inputs, outputs) = first List.transpose . unzip
      $ examples <&> \ex -> (ex.inputs, ex.output)

fromArgs :: [Constraint] -> Args -> Problem
fromArgs constraints (Args inputs (Arg goal outputs)) = Problem
  { signature = Signature
    { constraints
    , inputs = inputs <&> fmap (.mono)
    , output = goal
    }
  , examples = zipWith Example (exInputs ++ repeat []) outputs
  } where
    exInputs = List.transpose $ map (.value.terms) inputs

onArgs :: (Args -> Args) -> Problem -> Problem
onArgs f p = fromArgs p.signature.constraints . f $ toArgs p

restrict :: Set Text -> Args -> Args
restrict ss args =
  args { inputs = filter (\arg -> arg.name `Set.member` ss) args.inputs }

variables :: Problem -> [Text]
variables problem = problem.signature.inputs <&> (.name)

class Project a where
  projections :: a -> [a]

instance Project (Expr l h) where
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
  projections sig = do
    output <- projections sig.output
    return (sig { output } :: Signature)

instance Project Problem where
  projections prob = zipWith Problem ss bs
    where
      ss = projections prob.signature
      bs = List.transpose $ map projections prob.examples

instance Project Arg where
  projections = \case
    Arg (Product ts) es ->
      zipWith Arg ts . (++ repeat []) . List.transpose $ map projections es
    a -> [a]
