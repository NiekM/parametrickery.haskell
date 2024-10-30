{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Synth
  ( Synth
  , SynthC
  , Refinement
  , runRefinement
  , ProofState(..)
  , search
  , intro
  , tactics
  , applyTactic
  , auto, greedy
  , staged
  , combineFuns
  ) where

import Data.Map qualified as Map
import Data.List qualified as List

import Control.Effect.Fresh.Named
import Control.Effect.Weight
import Control.Carrier.Error.Either
import Control.Carrier.Reader
import Control.Carrier.State.Strict

import Data.PQueue.Max (MaxQueue)
import Data.PQueue.Max qualified as Queue

import Control.Monad.Search
import Control.Effect.Search ()

import Base
import Language.Type
import Language.Expr
import Language.Problem
import Language.Container.Morphism
import Language.Coverage
import Language.Relevance
import Language.Pretty

import Tactic
import Tactic.Combinators

data ProofState = ProofState
  { extracts :: [Named (Program Name)]
  , goals    :: [Named Problem]
  , unsolved :: MaxQueue Name
  , force    :: Bool
  } deriving stock (Eq, Ord, Show)

emptyProofState :: ProofState
emptyProofState = ProofState mempty mempty mempty False

instance Pretty ProofState where
  pretty ProofState { extracts, goals, unsolved } = statements
    [ statements $ pretty <$>
      filter (\g -> g.name `elem` Queue.toList unsolved) goals
    , pretty . fmap (norm mempty) . combineFuns $ extracts
    ]

type Synth sig m =
  ( Has (Reader Context) sig m
  , Has Fresh sig m
  , Has (State ProofState) sig m
  , Has Weight sig m
  , Has NonDet sig m
  , Alternative m
  )

-- TODO: can we generate some interactive search thing? Perhaps just an IO monad
-- where you select where to proceed and backtrack?
-- Perhaps use Gloss to render nodes of a tree, where each node shows one
-- refinement. Clicking on refinements explores them (if realizable) and perhaps
-- outputs the current state to the console? Or perhaps a next button that
-- explores the next node (based on its weight).
type SynthC = ReaderC Context (StateC ProofState (FreshC (Search (Sum Nat))))

search :: SynthC a -> Search (Sum Nat) a
search = evalFresh . evalState emptyProofState . runReader datatypes

type Refinement m = ReaderC Problem (ErrorC TacticFailure m) Filling

staged :: Synth sig m => m ProofState
staged = do
  st <- tactics auto
  let hs = holes (combineFuns st.extracts).value
  modify \s -> s { unsolved = Queue.fromList hs, force = True }
  tactics greedy

-- TODO: add synthesis options for stuff like this:
-- - whether to abort when out of tactics
-- - whether to allow totality checking on subspecifications
-- - whether to call a bottom-up synthesizer when e.g. only ints remain
tactics :: Synth sig m => [Refinement m] -> m ProofState
tactics [] = get
tactics (t:ts) = next >>= \case
  Nothing -> get
  Just (Named name problem) -> do
    applyTactic name problem t
    tactics ts

next :: Synth sig m => m (Maybe (Named Problem))
next = do
  ProofState { unsolved, goals } <- get
  case Queue.maxView unsolved of
    Nothing -> return Nothing
    Just (h, xs) -> case find h goals of
      Nothing -> error "unknown goal"
      Just g -> do
        modify \s -> s { unsolved = xs }
        return . Just $ Named h g

runRefinement :: Problem -> Refinement m -> m (Either TacticFailure Filling)
runRefinement problem tactic = runError $ runReader problem tactic

applyTactic :: Synth sig m => Name -> Problem -> Refinement m -> m ()
applyTactic name problem tactic =
  runRefinement problem tactic >>= \case
    Left NotApplicable -> empty
    Left TraceIncomplete -> empty
    Left (Unrealizable _conflict) -> empty
    Right program -> fill name program

fill :: Synth sig m => Name -> Filling -> m ()
fill name filling = do
  let (new, p') = names filling
  modify \s -> s { extracts = s.extracts ++ [Named name p'] }
  forM_ (Map.assocs new) $ subgoal . uncurry Named

intro :: Synth sig m => Named Problem -> m ()
intro problem = do
  let vars = variables problem.value
  applyTactic problem.name problem.value $ Lams vars <$> hole problem.name

subgoal :: Synth sig m => Named Problem -> m ()
subgoal (Named name problem) = do
  rules <- runError @Conflict (check problem) >>= \case
    Right r -> return r
    Left _ -> empty
  -- TODO: we could combine examples that lead to the same Rule.
  -- OR: similarly, we could reconstruct the problem by instantiating the rules.
  modify \s -> s { goals = Named name problem : s.goals }

  c <- coverage problem.signature rules
  r <- relevance problem
  -- Note that here we make the decision to accept a solution that ignores
  -- some of the input. This is a valid decision, but we should be very
  -- considerate about it, since it may lead to overfitting. By first checking
  -- that the input gives total coverage, we avoid this overfitting.
  -- We always make some assumptions about missing examples
  let
    -- NOTE: this leads to sometimes nicer solutions, but may also lead to
    -- overfitting. for example, head will be implemented as a fold if it is set
    -- to false, but as an elim (which is preferred) when set to true. on the
    -- other hand, this leads to overfitting for dupli, because we have too few
    -- cases.
    allowIgnoringInputs = False

    foo = asum $ r.relevance <&> \case
      (_, rs, Total) -> Just rs
      _ -> Nothing
    bar = case c of
      Total -> Just rules
      _ -> Nothing
  force <- gets @ProofState (.force)
  case (if allowIgnoringInputs then foo else bar) of
    Just _ | not force -> return ()
    _ -> modify \s -> s { unsolved = Queue.insert name s.unsolved }

-- TODO: use relevancy
-- TODO: totality check as a tactic
auto :: Synth sig m => [Refinement m]
auto = repeat $ anyOne assume <| asum
  [ anywhere \x ->
      (weigh 2 >> introMap x <| introFilter x <| (weigh 2 >> fold x))
      <|> (weigh 3 >> elim x)
  , weigh 3 >> anywhere2 \x y -> elimOrd x y <| elimEq x y
  , weigh 1 >> introCtr
  , weigh 0 >> introTuple
  ]

greedy :: Synth sig m => [Refinement m]
greedy = repeat $ firstOf
  [ anyOne assume
  , introTuple, introCtr
  , anyOne elim
  , anyTwo elimOrd, anyTwo elimEq
  ]

-- TODO: this is all just for handling extracts

fillHole :: Expr l Name -> Named (Expr l Name) -> Expr l Name
fillHole expr (Named name filling) = expr >>= \h ->
  if name == h then filling else Hole $ MkHole h

combineFuns :: [Named (Program Name)] -> Named (Program Name)
combineFuns [] = Named "" (Var "")
combineFuns xs = xs & List.foldl1' \x y -> fmap (`fillHole` y) x
