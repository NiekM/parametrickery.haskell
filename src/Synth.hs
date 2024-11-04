{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Synth
  ( Synth
  , SynthC
  , Refinement
  , search
  , runTac
  , auto, greedy
  ) where

import Control.Effect.Fresh.Named
import Control.Effect.Weight
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
type SynthC = ReaderC Context (FreshC (Search (Sum Nat)))

search :: Context -> SynthC a -> Search (Sum Nat) a
search ctx = evalFresh . runReader ctx

type Refinement m = ReaderC Problem (ErrorC TacticFailure m) Filling

runTac :: Synth sig m => Problem -> Refinement m -> m Filling
runTac problem tactic = do
  let vars = variables problem
  runError (runReader problem (Lams vars <$> tactic)) >>= \case
    Left NotApplicable -> empty
    Left TraceIncomplete -> empty
    Left (Unrealizable _conflict) -> empty
    Right program -> return program

-- TODO: use relevancy
auto :: Ref sig m => m Filling
auto = do
  problem <- ask @Problem
  rules <- runError @Conflict (check problem) >>= \case
    Right r -> return r
    Left _ -> empty
  coverage problem.signature rules >>= \case
    Total -> greedy
    _ -> anyOne assume <| asum
      [ anywhere \x ->
          (weigh 2 >> introMap x <| introFilter x <| (weigh 2 >> fold x))
          <|> (weigh 3 >> elim x)
      , weigh 3 >> anywhere2 \x y -> elimOrd x y <| elimEq x y
      , weigh 1 >> introCtr
      , weigh 0 >> introTuple
      ] `andThen` auto

greedy :: Ref sig m => m Filling
greedy = firstOf
  [ anyOne assume
  , introTuple
  , introCtr
  , weigh 1 >> anyOne elim
  , weigh 1 >> anyTwo elimOrd
  , weigh 1 >> anyTwo elimEq
  ] `andThen` greedy
