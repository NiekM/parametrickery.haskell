{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Language.Problem where

import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Set qualified as Set
import Data.Map qualified as Map
import Data.Functor qualified as Functor

import Base
import Language.Expr
import Language.Type
import Utils

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

disable :: Set Name -> Args -> Args
disable ss args = args { inputs = map enable args.inputs }
  where
    enable (Named name arg)
      | name `Set.notMember` ss = Named name arg
      | otherwise = Named name . Arg (Free "_") $ Unit <$ arg.terms

variables :: Problem -> [Name]
variables problem = problem.signature.inputs <&> (.name)

hide :: Name -> Problem -> Problem
hide name = onArgs \args -> args
  { inputs = filter (\arg -> arg.name /= name) args.inputs }

addInputs :: [Named Arg] -> Problem -> Problem
addInputs new = onArgs \args -> args { inputs = args.inputs ++ new }

inputArgs :: Problem -> [Named Arg]
inputArgs problem = (toArgs problem).inputs

outputArg :: Problem -> Arg
outputArg problem = (toArgs problem).output

named :: [Named a] -> Map Name a
named = Map.fromList . map \x -> (x.name, x.value)

split :: Context -> Arg -> Problem -> Maybe (Map Name (Arg, Problem))
split ctx (Arg (Data d ts) terms) (Problem signature examples) = do
  fields <- forM terms \case
    Ctr c x -> Just (c, x)
    _ -> Nothing
  let
    cs = named $ getConstructors d ts ctx
    paired = zipWith (fmap . (,)) examples fields
    m = NonEmpty.toList <$> gather paired
    (exs, vals) = Functor.unzip $ unzip <$> Map.union m ([] <$ cs)
    args = Map.intersectionWith Arg cs vals
    prbs = Problem signature <$> exs
  return $ Map.intersectionWith (,) args prbs
split _ _ _ = Nothing

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
