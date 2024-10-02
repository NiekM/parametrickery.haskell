{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Tactic where

import Data.Map qualified as Map
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty

import Data.Functor.Identity

import Control.Effect.Throw
import Control.Effect.Reader
import Control.Effect.Fresh.Named
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

pick :: Nat -> [a] -> Maybe (a, [a])
pick i xs = case List.genericSplitAt i xs of
  (ys, z:zs) -> Just (z, ys ++ zs)
  _ -> Nothing

pickArg :: Nat -> Problem -> Maybe (Named Arg, Problem)
pickArg n p = do
  let args = toArgs p
  (arg, inputs) <- pick n args.inputs
  return (arg, fromArgs p.signature.constraints args { inputs })

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

data SubGoal = SubGoal
  { name :: Text
  , problem :: Problem
  , rules :: [Rule]
  , coverage :: Coverage
  , relevance :: Relevance
  } deriving stock (Eq, Ord, Show)

instance Pretty SubGoal where
  pretty goal = statements
    [ pretty goal.problem.signature
    , statements $ map (prettyNamed goal.name) goal.rules
    , parens $ pretty goal.coverage
    , pretty goal.relevance
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

type TacticC = ReaderC Context (StateC ProofState
  (ErrorC Conflict (FreshC (NonDetC Identity))))

runTactic :: TacticC a -> [Either Conflict (ProofState, a)]
runTactic t = run . runNonDetA . evalFresh . runError
  . runState (ProofState Queue.empty) $ runReader datatypes t

execTactic :: TacticC a -> [Either Conflict ProofState]
execTactic t = run . runNonDetA . evalFresh . runError
  . execState (ProofState Queue.empty) $ runReader datatypes t

subgoal :: Tactic sig m => Text -> Problem -> m ()
subgoal t p = do
  rules <- check p
  name <- freshName t
  c <- coverage p.signature rules
  r <- relevance p
  let sub = SubGoal name p rules c r
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
-- TODO: catch errors and throw away unrealizable cases
folds :: Tactic sig m => Nat -> m ProofState
folds 0 = get
folds n = next >>= \case
  Nothing -> get
  Just goal -> do
    catchError @Conflict
      ( msum
        [ foldArgs goal.problem
        -- , introCons goal.problem
        , introCtr goal.problem
        , assumption goal.problem
        ]
      )
      (const mzero)
    folds (n - 1)

assumption :: Tactic sig m => Problem -> m ()
assumption problem = do
  (arg, _) <- oneOf $ pickApart problem
  guard $ arg.value == (toArgs problem).output

tuple :: Tactic sig m => Problem -> m ()
tuple problem = forM_ (projections problem) $ subgoal "_"

-- TODO: test this properly
introCtr :: Tactic sig m => Problem -> m ()
introCtr problem = case problem.signature.goal of
  Data d ts -> do
    cs <- asks $ getConstructors d ts
    -- TODO: getConstructor that returns the fields of one specific ctr
    exs <- forM problem.examples \example -> case example.output of
      Ctr c e -> (c,) <$> forM (projections e) \x ->
        return (example { output = x } :: Example)
      _ -> mzero
    case NonEmpty.groupAllWith fst exs of
      [] -> error "no examples"
      (_:_:_) -> mzero -- Not all examples agree.
      [xs] -> do
        let c = fst $ NonEmpty.head xs
        let exampless = List.transpose $ snd <$> NonEmpty.toList xs
        case List.find (\ct -> ct.name == c) cs of
          Nothing -> error "unknown constructor"
          Just ct -> do
            let goals = projections ct.field
            forM_ (zip exampless goals) \(examples, goal) -> do
              let signature = problem.signature { goal }
              subgoal "_" Problem { signature, examples }
  _ -> mzero

introCons :: Tactic sig m => Problem -> m ()
introCons problem = case problem.signature.goal of
  Data "List" [t] -> do
    exs <- forM problem.examples \example -> case example.output of
      Cons x xs -> return
        ( example { output = x  } :: Example
        , example { output = xs } :: Example
        )
      _ -> mzero
    let (hd, tl) = unzip exs
    subgoal "h" Problem
      { signature = problem.signature { goal = t }
      , examples = hd
      }
    subgoal "t" Problem
      { signature = problem.signature
      , examples = tl
      }
  _ -> mzero

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
      constrs <- forM paired \case
        (Nil, ex) -> return $ Left ex
        (Cons y ys, Example ins out) ->
          case recurse (ys:ins) of
            Nothing -> mzero
            Just r -> return . Right $ Example (ins ++ [y, r]) out
        _ -> error "Expected a list!"

      let (nil, cons) = partitionEithers constrs

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
      constrs <- forM paired \case
          (Ctr "Leaf" x, Example ins out) -> return . Left $
            Example (ins ++ [x]) out
          (Ctr "Node" (Tuple [l, x, r]), Example ins out) ->
            case (recurse (l:ins), recurse (r:ins)) of
              (Just left, Just right) -> return . Right $
                Example (ins ++ [left, x, right]) out
              _ -> mzero
          _ -> error "Expected a tree!"

      let (leaf, node) = partitionEithers constrs

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
