{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Tactic where

import Data.Map qualified as Map
import Data.Text qualified as Text
import Data.List qualified as List

import Data.Functor.Identity
import Control.Monad.Fail as Fail
import Control.Monad.Fix
import Control.Monad.IO.Class

import Control.Effect.Throw
import Control.Effect.Reader
import Control.Carrier.Error.Either
import Control.Carrier.Reader
import Control.Carrier.State.Strict
import Control.Carrier.NonDet.Church

import Data.PQueue.Max (MaxQueue)
import Data.PQueue.Max qualified as Queue

import Base
import Data.Named
import Language.Type
import Language.Expr
import Language.Problem
import Language.Container.Morphism
import Language.Coverage
import Language.Relevance
import Language.Pretty

import Utils

import Control.Algebra
import Data.Kind

pick :: Nat -> [a] -> Maybe (a, [a])
pick i xs = case List.genericSplitAt i xs of
  (ys, z:zs) -> Just (z, ys ++ zs)
  _ -> Nothing

pickInput :: Nat -> Example -> Maybe (Term, Example)
pickInput i (Example ins out) = fmap (`Example` out) <$> pick i ins

pickArg :: Nat -> Problem -> Maybe (Named Arg, Problem)
pickArg i (Problem sig exs) = do
  (t, context) <- pick i sig.context
  (xs, examples) <- mapAndUnzipM (pickInput i) exs
  return (fmap (`Arg` xs) t, Problem sig { context } examples)

-- All possible ways to pick one argument from a problem.
pickApart :: Problem -> [(Named Arg, Problem)]
pickApart p@(Problem Signature { context } _) =
  zipWith const [0..] context & mapMaybe (`pickArg` p)

addArgs :: [Named Arg] -> Problem -> Problem
addArgs [] p = p
addArgs args Problem { signature, examples } =
  Problem
    { signature = signature { context = signature.context ++ types }
    , examples = zipWith addInputs terms examples
    }
  where
    types = args <&> fmap (.mono)
    terms = List.transpose $ args <&> \x -> x.value.terms
    addInputs :: [Term] -> Example -> Example
    addInputs new (Example inputs output) = Example (inputs ++ new) output

data Fresh (m :: Type -> Type) a where
  Fresh :: Text -> Fresh m Nat

fresh :: Has Fresh sig m => Text -> m Nat
fresh t = send (Fresh t)

freshName :: Has Fresh sig m => Text -> m Text
freshName t = do
  n <- fresh t
  return $ t <> Text.pack (show n)

newtype FreshC m a = FreshC { runFreshC :: StateC (Map Text Nat) m a }
  deriving newtype (Alternative, Applicative, Functor, Monad, Fail.MonadFail, MonadFix, MonadIO, MonadPlus)

evalFresh :: Functor m => FreshC m a -> m a
evalFresh (FreshC s) = evalState mempty s

instance Algebra sig m => Algebra (Fresh :+: sig) (FreshC m) where
  alg hdl sig ctx = FreshC $ case sig of
    L (Fresh t) -> do
      m <- get
      let n = fromMaybe 0 $ Map.lookup t m
      modify $ Map.insert t (n + 1)
      return (n <$ ctx)
    R other -> alg ((.runFreshC) . hdl) (R other) ctx

data SubGoal = SubGoal
  { name :: Text
  , signature :: Signature
  , examples :: [Example]
  , polymorphic :: [Rule]
  , coverage :: Coverage
  , relevance :: Relevance
  } deriving stock (Eq, Ord, Show)

subProblem :: SubGoal -> Problem
subProblem g = Problem g.signature g.examples

instance Pretty SubGoal where
  pretty g = statements
    [ pretty g.signature
    , statements $ map (prettyNamed g.name) g.polymorphic
    , parens $ pretty g.coverage
    , pretty g.relevance
    ]

newtype ProofState = ProofState
  -- TODO: we probably want to remember all subgoals, but keep a separate queue
  -- of unresolved subgoals to handle.
  { subgoals :: MaxQueue SubGoal
  } deriving stock (Eq, Ord, Show)

instance Pretty ProofState where
  pretty p = statements $ pretty <$> Queue.toList p.subgoals

type Tactic sig m =
  ( Has (Reader Context) sig m
  , Has Fresh sig m
  , Has (Error Conflict) sig m
  , Has (State ProofState) sig m
  , Has NonDet sig m
  , MonadPlus m
  )

runTactic :: ReaderC Context (StateC ProofState (ErrorC Conflict (FreshC (NonDetC Identity)))) a -> [Either Conflict (ProofState, a)]
runTactic t = run . runNonDetA . evalFresh . runError
  . runState (ProofState Queue.empty) $ runReader datatypes t

execTactic :: ReaderC Context (StateC ProofState (ErrorC Conflict (FreshC (NonDetC Identity)))) a -> [Either Conflict ProofState]
execTactic t = run . runNonDetA . evalFresh . runError
  . execState (ProofState Queue.empty) $ runReader datatypes t

subgoal :: Tactic sig m => Text -> Problem -> m ()
subgoal t p = do
  p' <- check p
  name <- freshName t
  c <- coverage p.signature p'
  r <- relevance p
  let sub = SubGoal name p.signature p.examples p' c r
  modify \s -> s { subgoals = Queue.insert sub s.subgoals }

next :: Tactic sig m => m (Maybe SubGoal)
next = do
  gs <- gets @ProofState (.subgoals)
  case Queue.maxView gs of
    Nothing -> return Nothing
    Just (x, xs) -> do
      modify \s -> s { subgoals = xs }
      case x.coverage of
        Total -> next
        _ -> return $ Just x

-- TODO: deal with trace incompleteness: do we just disallow fold?
-- TODO: implement relevancy check
folds :: Tactic sig m => Nat -> m ProofState
folds 0 = get
folds n = do
  x <- next
  case x of
    Nothing -> get
    Just g -> do
      foldArgs $ subProblem g
      folds (n - 1)

tuple :: Tactic sig m => Problem -> m ()
tuple problem = forM_ (projections problem) $ subgoal "_"

caseSplit :: Has (Reader Context) sig m =>
  Named Arg -> Problem -> m (Map Text (Named Arg, Problem))
caseSplit (Named name (Arg (Data d ts) terms)) prob = do
  cs <- asks $ getConstructors d ts
  let
    e = Map.fromList $ cs <&> \c ->
      ( c.name
      , ( Named (name <> "_" <> c.name) (Arg c.field [])
        , Problem prob.signature []
        )
      )

    f m (Ctr c x, ex) = Map.adjust (bimap
      (\(Named v (Arg ty ys)) -> Named v (Arg ty (x:ys)))
      (\(Problem sig exs) -> Problem sig (ex:exs))) c m
    f _ _ = error "Not a constructor"

  return $ List.foldl' f e (zip terms prob.examples)
caseSplit _ _ = error "Not a datatype"

split :: Tactic sig m => Named Arg -> Problem -> m ()
split arg problem = do
  m <- caseSplit arg problem
  forM_ (Map.elems m) \(Named v a, p) -> do
    as <- forM (projections a) \x -> do
      name <- freshName v
      return $ Named name x
    subgoal v $ addArgs as p

introMap :: Tactic sig m => Named Arg -> Problem -> m ()
introMap (Named _ (Arg ty terms)) problem = case (ty, problem.signature.goal) of
  (Data "List" [t], Data "List" [u]) -> do
    examples <- forM (zip terms problem.examples) \case
      (List inputs, Example scope (List outputs)) -> do
        guard $ length inputs == length outputs
        return $ zipWith (\x y -> Example (scope ++ [x]) y) inputs outputs
      _ -> error "Not actually lists."
    x <- freshName "x"
    let Signature constraints context _ = problem.signature
    let signature = Signature constraints (context ++ [Named x t]) u
    subgoal "f" $ Problem signature (concat examples)
  _ -> mzero

foldArgs :: Tactic sig m => Problem -> m ()
foldArgs problem = do
  (arg, prob) <- oneOf $ pickApart problem
  fold arg prob

fold :: Tactic sig m => Named Arg -> Problem -> m ()
fold (Named name (Arg ty terms)) problem = do

  let paired = zip terms problem.examples
  rules <- check Problem
    { signature = problem.signature
      { context = Named name ty : problem.signature.context }
    , examples = paired <&> \(i, Example is o) -> Example (i:is) o
    }
  let recurse = applyRules rules

  case ty of
    Data "List" [t] -> do 
      let
        (nil, cons) = paired & mapEither \case
          (Nil, ex) -> Left ex
          (Cons y ys, Example ins out) ->
            case recurse (ys:ins) of
              -- TODO: how do we collect missing inputs?
              Nothing -> error "Not shape complete!"
              Just r -> return $ Example (ins ++ [y, r]) out
          _ -> error "Expected a list!"

      subgoal "e" $ problem { examples = nil }

      x <- freshName "x"
      r <- freshName "r"
      subgoal "f" $ Problem problem.signature
        { context = problem.signature.context ++
          [ Named x t
          , Named r problem.signature.goal
          ]
        } cons

    Data "Tree" [t, u] -> do
      let
        (leaf, node) = paired & mapEither \case
          (Ctr "Leaf" x, Example ins out) -> Left (Example (ins ++ [x]) out)
          (Ctr "Node" (Tuple [l, x, r]), Example ins out) ->
            case (recurse (l:ins), recurse (r:ins)) of
              (Just left, Just right) -> return $
                Example (ins ++ [left, x, right]) out
              _ -> error "Not shape complete!"
          _ -> error "Expected a tree!"

      y <- freshName "y"
      subgoal "e" $ Problem problem.signature
        { context = problem.signature.context ++ [ Named y u ] } leaf

      l <- freshName "l"
      x <- freshName "x"
      r <- freshName "r"
      subgoal "f" $ Problem problem.signature
        { context = problem.signature.context ++
          [ Named l problem.signature.goal
          , Named x t
          , Named r problem.signature.goal
          ]
        } node

    _ -> mzero
