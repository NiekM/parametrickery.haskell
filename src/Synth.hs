{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Synth
  ( synthesize
  , Solution(..)
  , SynthFailure(..)
  , Extract(..)
  , Arguments(..)
  , def
  , Synth
  , SynthC
  , Refinement
  , search
  , runTac
  , step, greedyStep
  , auto, greedy
  , extraGreedy
  ) where

import Control.Effect.Fresh.Named
import Control.Effect.Weight
import Control.Effect.Search
import Control.Carrier.Error.Either
import Control.Carrier.Reader

import Control.Monad.Search
import Control.Effect.Search ()

import Base hiding (repeat)
import Language.Type
import Language.Expr
import Language.Problem

import Tactic
import Tactic.Combinators
import Tactic.Predicate
import Tactic.Map qualified as Tactic
import Tactic.Filter qualified as Tactic
import Tactic.Fold qualified as Tactic
import Tactic.Relation qualified as Tactic

import Language.Prelude
import Language.Pretty
import Data.List qualified as List

import Utils

data Arguments = Arguments
  { tactic :: Refinement SynthC
  , fuel :: Maybe Nat
  , solutions :: Maybe Nat
  , settings :: Settings
  , context :: Context
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
    searchSpace = search args.settings args.context
      . maybe (fmap Just) limit args.fuel
      $ runTac problem (hole True `andThen` args.tactic)

type Synth sig m =
  ( Has (Reader Context) sig m
  , Has Fresh sig m
  , Has Weight sig m
  , Has Choose sig m
  )

type Ref sig m =
  ( Synth sig m
  , Tactic sig m
  , Has (Catch TacticFailure) sig m
  )

-- TODO: can we generate some interactive search thing? Perhaps just an IO monad
-- where you select where to proceed and backtrack?
-- Perhaps use Gloss to render nodes of a tree, where each node shows one
-- refinement. Clicking on refinements explores them (if realizable) and perhaps
-- outputs the current state to the console? Or perhaps a next button that
-- explores the next node (based on its weight).
type SynthC = ReaderC Settings (ReaderC Context (FreshC (Search (Sum Nat))))

search :: Settings -> Context -> SynthC a -> Search (Sum Nat) a
search settings ctx = evalFresh . runReader ctx . runReader settings

type Refinement m = ReaderC Problem (ErrorC TacticFailure m) Filling

runTac :: Synth sig m => Problem -> Refinement m -> m (Either TacticFailure Filling)
runTac problem tactic = do
  let vars = variables problem
  runError . runReader problem $ Lams vars <$> tactic

-- TODO: use relevancy
-- TODO: normalize problems by removing examples that are equivalent
-- TODO: do we want to use weights? it might be nicer to add those later,
--       if we add labels we can then use those to weigh the search.

-- * Larger tactic groups

constructors :: Ref sig m => m Filling
constructors = introCtr <| introTuple

eliminators :: Ref sig m => Name -> m Filling
eliminators x = Tactic.map x <| Tactic.filter x <| Tactic.fold x <| Tactic.para x <| elim x

relations :: Ref sig m => Name -> Name -> m Filling
relations x y = Tactic.elimOrd x y <| Tactic.elimEq x y

-- * Single steps

step :: Ref sig m => m Filling
step = anywhere assume <| anyOf
  [ everywhere eliminators
  , everywhere2 relations
  , constructors
  ]

greedyStep :: Ref sig m => m Filling
greedyStep = firstOf
  [ anywhere assume
  , constructors
  , anywhere elim
  , anywhere2 relations
  ]

-- * Synthesizers

phase1 :: Ref sig m => m Filling
phase1 = until covering step

auto :: Ref sig m => m Filling
auto = phase1 >>> greedy

greedy :: Ref sig m => m Filling
greedy = repeat greedyStep

extraGreedy :: Ref sig m => m Filling
extraGreedy = until noExamples greedyStep

-- * Old versions with weights

-- greedyStep :: Ref sig m => m Filling
-- greedyStep = firstOf
--   [ anyOne assume
--   , introTuple
--   , introCtr
--   , weigh 1 >> anyOne elim
--   , weigh 1 >> anyTwo Tactic.elimOrd
--   , weigh 1 >> anyTwo Tactic.elimEq
--   ]

-- step :: Ref sig m => m Filling
-- step = anyOne assume <| asum
--   [ anywhere \x ->
--       -- Alternative tactic: use para if fold does not work, and use elim if its not a recursive datatype.
--       (weigh 2 >> Tactic.map x <| Tactic.filter x <| (weigh 2 >> Tactic.fold x <| Tactic.para x <| elim x))
--       -- (weigh 2 >> Tactic.map x <| Tactic.filter x <| (weigh 2 >> Tactic.fold x))
--       -- <|> (weigh 3 >> elim x)
--   , weigh 3 >> anywhere2 \x y -> Tactic.elimOrd x y <| Tactic.elimEq x y
--   , weigh 1 >> introCtr
--   , weigh 0 >> introTuple
--   ]
