{-# LANGUAGE UndecidableInstances #-}

module Tactic where

import Data.Map qualified as Map
import Data.Text qualified as Text
import Data.List qualified as List

import Control.Effect.Throw
import Control.Effect.Reader
import Control.Carrier.Throw.Either
import Control.Carrier.Reader
import Control.Carrier.State.Strict
import Control.Carrier.NonDet.Church

import Data.Functor.Identity
import Control.Monad.Fail as Fail
import Control.Monad.Fix
import Control.Monad.IO.Class

import Base
import Data.Named
import Language.Type
import Language.Expr
import Language.Declaration
import Language.Container.Morphism
import Language.Coverage

import Utils
import Prettyprinter.Utils

import Control.Algebra
import Data.Kind

pick :: Nat -> [a] -> Maybe (a, [a])
pick i xs = case List.genericSplitAt i xs of
  (ys, z:zs) -> Just (z, ys ++ zs)
  _ -> Nothing

pickInput :: Nat -> Example -> Maybe (Term, Example)
pickInput i (Example ins out) = fmap (`Example` out) <$> pick i ins

pickArg :: Nat -> Problem -> Maybe (Named Arg, Problem)
pickArg i (Declaration sig exs) = do
  (t, context) <- pick i sig.context
  (xs, examples) <- mapAndUnzipM (pickInput i) exs
  return (fmap (, xs) t, Declaration sig { context } examples)

-- All possible ways to pick one argument from a problem.
pickApart :: Problem -> [(Named Arg, Problem)]
pickApart p@(Declaration Signature { context } _) =
  zipWith const [0..] context & mapMaybe (`pickArg` p)

addArgs :: [Named Arg] -> Problem -> Problem
addArgs [] p = p
addArgs args Declaration { signature, bindings } =
  Declaration
    { signature = signature { context = signature.context ++ types }
    , bindings = zipWith addInputs terms bindings
    }
  where
    types = args <&> fmap fst
    terms = List.transpose $ args <&> \x -> snd x.value
    addInputs :: [Term] -> Example -> Example
    addInputs new (Example inputs output) = Example (inputs ++ new) output

data Fresh (m :: Type -> Type) a where
  Fresh :: Text -> Fresh m Nat

fresh :: Has Fresh sig m => Text -> m Nat
fresh t = send (Fresh t)

freshName :: Has Fresh sig m => Text -> m Text
freshName t = do
  n <- fresh t
  return case n of
    0 -> t
    _ -> t <> Text.pack (show n)

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
  , polymorphic :: [PolyExample]
  , coverage :: Coverage
  } deriving stock (Eq, Ord, Show)

subProblem :: SubGoal -> Problem
subProblem g = Declaration g.signature g.examples

instance Pretty SubGoal where
  pretty g = statements [pretty problem, parens $ pretty g.coverage]
    where problem = Named g.name $ Declaration g.signature g.polymorphic

newtype ProofState = ProofState
  { subgoals :: [SubGoal]
  } deriving stock (Eq, Ord, Show)

instance Pretty ProofState where
  pretty p = statements $ pretty <$> p.subgoals

type Tactic sig m =
  ( Has (Reader Context) sig m
  , Has Fresh sig m
  , Has (Throw Conflict) sig m
  , Has (State ProofState) sig m
  , Has NonDet sig m
  , MonadPlus m
  )

runTactic :: ReaderC Context (StateC ProofState (ThrowC Conflict (FreshC (NonDetC Identity)))) a -> [Either Conflict (ProofState, a)]
runTactic t = run . runNonDetA . evalFresh . runThrow
  . runState (ProofState []) $ runReader datatypes t

execTactic :: ReaderC Context (StateC ProofState (ThrowC Conflict (FreshC (NonDetC Identity)))) a -> [Either Conflict ProofState]
execTactic t = run . runNonDetA . evalFresh . runThrow
  . execState (ProofState []) $ runReader datatypes t

subgoal :: Tactic sig m => Text -> Problem -> m ()
subgoal t p = do
  p' <- check p
  name <- freshName t
  c <- coverage p'
  let sub = SubGoal name p.signature p.bindings p'.bindings c
  modify \(ProofState xs) -> ProofState (sub:xs)

tuple :: Tactic sig m => Problem -> m ()
tuple problem = forM_ (projections problem) $ subgoal "_"

caseSplit :: Has (Reader Context) sig m =>
  Named Arg -> Problem -> m (Map Text (Named Arg, Problem))
caseSplit (Named name (Data d ts, terms)) prob = do
  cs <- asks $ getConstructors d ts
  let
    e = Map.fromList $ cs <&> \c ->
      ( c.name
      , ( Named (name <> "_" <> c.name) (c.field, [])
        , Declaration prob.signature []
        )
      )

    f m (Ctr c x, ex) = Map.adjust (bimap
      (\(Named v (ty, ys)) -> Named v (ty, x:ys))
      (\(Declaration sig exs) -> Declaration sig (ex:exs))) c m
    f _ _ = error "Not a constructor"

  return $ List.foldl' f e (zip terms prob.bindings)
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
introMap (Named _ (ty, terms)) problem = case (ty, problem.signature.goal) of
  (Data "List" [t], Data "List" [u]) -> do
    exs <- forM (zip terms problem.bindings) \case
      (List inputs, Example scope (List outputs)) -> do
        guard $ length inputs == length outputs
        return $ zipWith (\x y -> Example (scope ++ [x]) y) inputs outputs
      _ -> error "Not actually lists."
    x <- freshName "x"
    let Signature constraints context _ = problem.signature
    let signature = Signature constraints (context ++ [Named x t]) u
    subgoal "f" $ Declaration signature (concat exs)
  _ -> mzero

foldArgs :: Tactic sig m => Problem -> m ()
foldArgs problem = do
  (arg, prob) <- oneOf $ pickApart problem
  fold arg prob

fold :: Tactic sig m => Named Arg -> Problem -> m ()
fold (Named name (ty, terms)) problem = do

  let paired = zip terms problem.bindings
  polyProblem <- check Declaration
    { signature = problem.signature
      { context = Named name ty : problem.signature.context }
    , bindings = paired <&> \(i, Example is o) -> Example (i:is) o
    }
  let recurse = applyProblem polyProblem

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

      subgoal "e" $ problem { bindings = nil }

      x <- freshName "x"
      r <- freshName "r"
      subgoal "f" $ Declaration problem.signature
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
      subgoal "e" $ Declaration problem.signature
        { context = problem.signature.context ++ [ Named y u ] } leaf

      l <- freshName "l"
      x <- freshName "x"
      r <- freshName "r"
      subgoal "f" $ Declaration problem.signature
        { context = problem.signature.context ++
          [ Named l problem.signature.goal
          , Named x t
          , Named r problem.signature.goal
          ]
        } node

    _ -> mzero
