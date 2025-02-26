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
  ) where

import Control.Effect.Fresh.Named
import Control.Effect.Weight
import Control.Effect.Search
import Control.Carrier.Error.Either
import Control.Carrier.Reader

import Control.Monad.Search
import Control.Effect.Search ()

import Base
import Language.Type
import Language.Expr
import Language.Problem
import Language.Container.Morphism
import Language.Coverage

import Tactic.Combinators
import Tactic
import Tactic.Map qualified as Tactic
import Tactic.Filter qualified as Tactic
import Tactic.Fold qualified as Tactic
import Tactic.Relation qualified as Tactic

import Language.Prelude
import Data.List qualified as List
import Prettyprinter

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
    Unfinished filling -> prettySplit filling

data Solution
  = Success (NonEmpty (Nat, Extract))
  | Failure SynthFailure
  deriving stock (Eq, Ord, Show)

instance Pretty Solution where
  pretty = \case
    Success ((_, extr) :| []) -> pretty extr
    Success extracts -> pretty . toList $ fmap snd extracts
    Failure failure -> pretty failure

prettySplit :: (Pretty h, Pretty (Named h)) => Expr l (Named h) -> Doc ann
prettySplit e
  | null helpers = pretty e
  | otherwise = nest 2 $ vsep
    [ pretty $ fmap (.name) e
    , nest 2 . vsep $ "where"
      : List.intersperse "" helpers
    ]
  where helpers = map pretty $ holes e

takeWhileJust :: [Maybe a] -> [a]
takeWhileJust = foldr (maybe (const []) (:)) []

synthesize :: Arguments -> Problem -> Solution
synthesize args problem = case runSearch searchSpace of
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
    toExtract :: Filling -> Extract
    toExtract filling =
      let normalized = normalize filling
      in case vacant normalized of
        Nothing -> Unfinished normalized
        Just program -> Finished program

    searchSpace :: Search (Sum Nat) (Maybe Filling)
    searchSpace = search args.settings args.context
      . maybe (fmap Just) limit args.fuel
      $ runTac problem (hole True `andThen` args.tactic)

type Synth sig m =
  ( Has (Reader Context) sig m
  , Has Fresh sig m
  , Has Weight sig m
  , Has NonDet sig m
  , Alternative m
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

runTac :: Synth sig m => Problem -> Refinement m -> m Filling
runTac problem tactic = do
  let vars = variables problem
  runError (runReader problem (Lams vars <$> tactic)) >>= \case
    Left (NotApplicable _message) -> empty
    Left TraceIncomplete -> empty
    Left (PropagationError _message) -> empty
    Left (Unrealizable _conflict) -> empty
    Right program -> return program

-- TODO: use relevancy
-- TODO: normalize problems by removing examples that are equivalent
step :: Ref sig m => m Filling
step = do
  problem <- ask @Problem
  rules <- runError @Conflict (check problem) >>= \case
    Right r -> return r
    Left _ -> empty
  coverage problem.signature rules >>= \case
    Total -> greedy
    _ -> anyOne assume <| asum
      [ anywhere \x ->
          (weigh 2 >> Tactic.map x <| Tactic.filter x <| (weigh 2 >> Tactic.fold x))
          <|> (weigh 3 >> elim x)
      , weigh 3 >> anywhere2 \x y -> Tactic.elimOrd x y <| Tactic.elimEq x y
      , weigh 1 >> introCtr
      , weigh 0 >> introTuple
      ]

auto :: Ref sig m => m Filling
auto = step `andThen` auto

greedyStep :: Ref sig m => m Filling
greedyStep = firstOf
  [ anyOne assume
  , introTuple
  , introCtr
  , weigh 1 >> anyOne elim
  , weigh 1 >> anyTwo Tactic.elimOrd
  , weigh 1 >> anyTwo Tactic.elimEq
  ]

greedy :: Ref sig m => m Filling
greedy = greedyStep `andThen` greedy
