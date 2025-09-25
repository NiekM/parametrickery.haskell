{-# OPTIONS_GHC -Wno-ambiguous-fields #-}
{-# LANGUAGE OverloadedLists #-}

module Synth
  ( synthesize
  , Solution(..)
  , SynthFailure(..)
  , Extract(..)
  , Arguments(..)
  , def
  , Synth
  , SynthC
  , step
  , auto
  , runTactic
  ) where

import Control.Effect.Fresh.Named
import Control.Effect.Search
import Control.Carrier.Error.Either
import Control.Carrier.Reader

import Control.Monad.Search

import Base hiding (repeat)
import Language.Type
import Language.Expr
import Language.Problem

import Tactic
import Tactic.Combinators
import Tactic.Map qualified as Tactic
import Tactic.Filter qualified as Tactic
import Tactic.Fold qualified as Tactic

import Language.Prelude
import Language.Pretty
import Data.List qualified as List

import Utils
import Data.Functor.Identity (Identity)

data Arguments = Arguments
  { tactic :: SynthC Filling
  , fuel :: Maybe Nat
  , solutions :: Maybe Nat
  , settings :: Settings
  , context :: DataContext
  }

def :: Arguments
def = Arguments
  { tactic = auto
  , fuel = Nothing
  , solutions = Just 1
  , settings = defaultSettings
  , context = datatypes
  }

data SynthFailure
  = Exhausted -- out of programs
  | Depleted -- out of fuel
  deriving stock (Eq, Ord, Show)

instance Pretty SynthFailure where
  pretty = \case
    Exhausted -> "Exhausted"
    Depleted -> "Depleted"

data Extract
  = Finished (Program Void)
  | Unfinished Filling
  deriving stock (Eq, Ord, Show)

instance Pretty Extract where
  pretty = \case
    Finished program -> pretty program
    Unfinished filling -> pretty . Split $ withNames "_" filling

data Solution
  = Success (NonEmpty (Nat, Extract))
  | Failure SynthFailure
  deriving stock (Eq, Ord, Show)

instance Pretty Solution where
  pretty = \case
    Success ((_, extr) :| []) -> pretty extr
    Success extracts -> pretty . toList $ fmap snd extracts
    Failure failure -> pretty failure

takeWhileJust :: [Maybe a] -> [a]
takeWhileJust = foldr (maybe (const []) (:)) []

synthesize :: Arguments -> Problem -> Solution
synthesize args problem = case dropFailures $ runSearch searchSpace of
  [] -> Failure Exhausted
  -- TODO: when we add a fuel limit, it says depleted even if it should be
  -- exhausted. How do we distinguish between them?
  xs ->
    let take = maybe id List.genericTake args.solutions
    in case take . takeWhileJust $ map sequence xs of
    [] -> Failure Depleted
    (y:ys) -> Success $ (y :| ys) <&> \(Sum weight, filling) ->
      (weight, toExtract filling)
  where
    dropFailures :: [(Sum Nat, Maybe (Either a b))] -> [(Sum Nat, Maybe b)]
    dropFailures = mapMaybe $ traverse . traverse $ either (const Nothing) (Just)

    toExtract :: Filling -> Extract
    toExtract filling =
      let normalized = normalize filling
      in case vacant normalized of
        Nothing -> Unfinished normalized
        Just program -> Finished program

    searchSpace :: Search (Sum Nat) (Maybe (Either TacticFailure Filling))
    searchSpace = maybe (fmap Just) limit args.fuel
      . evalFresh
      . runError
      . runReader args.context
      . runReader args.settings
      . runReader problem
      $ Lams (variables problem) <$> (rerealize hole >>> args.tactic)

type Synth sig m = (Tactic sig m, Has Choose sig m)

-- TODO: can we generate some interactive search thing? Perhaps just an IO monad
-- where you select where to proceed and backtrack?
-- Perhaps use Gloss to render nodes of a tree, where each node shows one
-- refinement. Clicking on refinements explores them (if realizable) and perhaps
-- outputs the current state to the console? Or perhaps a next button that
-- explores the next node (based on its weight).

type TacticC m = ReaderC Problem (ReaderC Settings (ReaderC DataContext (ErrorC TacticFailure (FreshC m))))

type SynthC = TacticC (Search (Sum Nat))

runTactic :: Settings -> DataContext -> Problem -> TacticC (IgnoreC Identity) Filling -> Either TacticFailure Filling
runTactic settings context problem tactic = do
  let vars = variables problem
  run . ignoreWeight . evalFresh . runError . runReader context . runReader settings . runReader problem $ Lams vars <$> tactic

-- TODO: use relevancy
-- TODO: normalize problems by removing examples that are equivalent
-- TODO: do we want to use weights? it might be nicer to add those later,
--       if we add labels we can then use those to weigh the search.

-- * Larger tactic groups

eliminators :: Synth sig m => Name -> m Filling
eliminators x = Tactic.map x <| Tactic.filter x <| Tactic.fold x <| Tactic.para x <| elim x

-- * Single steps

step :: Synth sig m => m Filling
step = anywhere assume <| anyOf
  [ everywhere eliminators
  , everywhere2 relations
  , constructors
  ]

-- * Synthesizers

auto :: Synth sig m => m Filling
auto = repeat step
