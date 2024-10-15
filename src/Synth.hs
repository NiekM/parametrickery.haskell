{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Synth
  ( Synth
  , Extract(..)
  , Spec(..)
  , ProofState(..)
  , search
  , auto
  , goal
  , next
  , extrs
  , applyTactic
  , anywhere
  ) where

import Data.Map qualified as Map
import Data.List qualified as List

import Control.Effect.Throw
import Control.Effect.Reader
import Control.Effect.Fresh.Named
import Control.Effect.Weight
import Control.Carrier.Error.Either
import Control.Carrier.Reader
import Control.Carrier.State.Strict
import Control.Carrier.NonDet.Church

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

import Language.Container.Relation
import Utils
import Data.Maybe (fromJust)
import Data.Set qualified as Set
import Data.Map.Multi qualified as Multi
import Tactic

data Extract = Fun (Program Name) | Rules [Rule]
  deriving stock (Eq, Ord, Show)

instance Pretty Extract where
  pretty = \case
    Fun p -> pretty p
    Rules r -> statements $ map pretty r

instance Pretty (Named Extract) where
  pretty (Named name extr) = case extr of
    Fun p -> prettyNamed name p
    Rules r -> statements $ prettyNamed name <$> r

data Spec = Spec
  { problem :: Problem
  , rules :: [Rule]
  , coverage :: Coverage
  , relevance :: Relevance
  } deriving stock (Eq, Ord, Show)

instance Pretty Spec where
  pretty = prettyNamed "_"

instance Pretty (Named Spec) where
  pretty (Named name spec) = statements
    [ prettyNamed name spec.problem.signature
    , statements $ map (prettyNamed name) spec.rules
    , parens $ pretty spec.coverage
    ]

data ProofState = ProofState
  { toplevel :: [Name]
  , extract  :: [Named Extract]
  , goals    :: [Named Spec]
  , unsolved :: MaxQueue Name
  } deriving stock (Eq, Ord, Show)

emptyProofState :: ProofState
emptyProofState = ProofState mempty mempty mempty mempty

instance Pretty ProofState where
  pretty p = statements $ pretty <$> p.goals

type Synth sig m =
  ( Has (Reader Context) sig m
  , Has Fresh sig m
  , Has (State ProofState) sig m
  , Has Weight sig m
  , Has NonDet sig m
  , MonadPlus m
  )

-- TODO: can we generate some interactive search thing? Perhaps just an IO monad
-- where you select where to proceed and backtrack?
-- Perhaps use Gloss to render nodes of a tree, where each node shows one
-- refinement. Clicking on refinements explores them (if realizable) and perhaps
-- outputs the current state to the console? Or perhaps a next button that
-- explores the next node (based on its weight).
type SearchC = ReaderC Context (StateC ProofState (FreshC (Search (Sum Nat))))

search :: SearchC a -> Search (Sum Nat) ProofState
search t = evalFresh . execState emptyProofState $ runReader datatypes t

goal :: Synth sig m => Named Problem -> m ()
goal problem = do
  modify \s -> s { toplevel = problem.name : s.toplevel}
  subgoal problem

type TacticC m = ReaderC Problem (ErrorC Conflict (ErrorC TacticFailure m))

applyTactic :: Synth sig m => Named Problem ->
  TacticC m (Program (Named Problem)) -> m ()
applyTactic (Named name problem) m =
  runError (runError (runReader problem m)) >>= \case
    Left NotApplicable -> mzero
    Left TraceIncomplete -> mzero
    Right (Left _conflict) -> mzero
    Right (Right program) -> Synth.fill name program

names :: Traversable f => f (Named v) -> (Map Name v, f Name)
names = traverse \(Named name x) -> (Map.singleton name x, name)

fill :: Synth sig m => Name -> Program (Named Problem) -> m ()
fill name filling = do
  ProofState { goals } <- get
  case find name goals of
    Nothing -> error "Unknown hole"
    Just spec -> do
      let (new, p') = names filling
      let vars = variables spec.problem
      modify \s -> s { extract =
        s.extract ++ [Named name . Fun $ lams vars p'] }
      forM_ (Map.assocs new) $ subgoal . uncurry Named

subgoal :: Synth sig m => Named Problem -> m ()
subgoal (Named name p) = do
  rules <- runError @Conflict (check p) >>= \case
    Right r -> return r
    -- TODO: somehow report conflicts
    Left _ -> mzero
  c <- coverage p.signature rules
  r <- relevance p
  let sub = Named name $ Spec p rules c r
  modify \s -> s { goals = sub : s.goals }
  -- Note that here we make the decision to accept a solution that ignores
  -- some of the input. This is a valid decision, but we should be very
  -- considerate about it, since it may lead to overfitting. By first checking
  -- that the input gives total coverage, we avoid this overfitting.
  -- We always make some assumptions about missing examples
  let
    allowIgnoringInputs = True

    foo = msum $ r.relevance <&> \case
      (_, rs, Total) -> Just rs
      _ -> Nothing
    bar = case c of
      Total -> Just rules
      _ -> Nothing
  case (if allowIgnoringInputs then foo else bar) of
    Just rs -> modify \s -> s { extract = s.extract ++ [Named name $ Rules rs] }
    _ -> modify \s -> s { unsolved = Queue.insert name s.unsolved }

next :: Synth sig m => m (Maybe (Named Spec))
next = do
  ProofState { unsolved, goals } <- get
  case Queue.maxView unsolved of
    Nothing -> return Nothing
    Just (hole, xs) -> case find hole goals of
      Nothing -> error "unknown goal"
      Just g -> do
        modify \s -> s { unsolved = xs }
        return . Just $ Named hole g

flatten :: Problem -> Problem
flatten = onArgs \args ->
  let
    scope = args.inputs >>= \(Named name arg) -> split (Var name, arg)

    split :: (Program Void, Arg) -> [(Program Void, Arg)]
    split (expr, arg) = case arg.mono of
      Product _ -> concat $ zipWith (\i e -> split (Prj i expr, e))
        [0..] (projections arg)
      _ -> [(expr, arg)]

    inputs = scope <&> \(x, a) -> Named (fromString . show $ pretty x) a

  in Args inputs args.output

-- TODO: use relevancy
auto :: Synth sig m => Nat -> m ProofState
auto 0 = mzero
auto n = next >>= \case
  Nothing -> get
  Just spec -> do
    let subproblem = flatten . (.problem) <$> spec
    applyTactic subproblem $ msum
      [ weigh 4 >> anywhere fold
      , weigh 2 >> anywhere elim
      , weigh 1 >> introCtr
      , weigh 0 >> introTuple
      , weigh 0 >> anywhere assume
      ]
    auto (n - 1)

anywhere :: (Tactic sig m, MonadPlus m) => (Name -> m a) -> m a
anywhere tactic = do
  name <- oneOf =<< asks variables
  tactic name

fillHole :: Expr l Name -> Named (Expr l Name) -> Expr l Name
fillHole expr (Named name filling) = expr >>= \h ->
  if name == h then filling else Hole $ MkHole h

combineFuns :: [Named (Program Name)] -> Named (Program Name)
combineFuns [] = Named "" (Var "")
combineFuns xs = xs & List.foldl1' \x y -> fmap (`fillHole` y) x

isHole :: Expr l h -> Maybe h
isHole (Hole (MkHole h)) = Just h
isHole _ = Nothing

fromRules :: Named [Rule] -> Maybe (Named (Program Name))
fromRules = mapM \case
  [rule]
    | not $ any relevant rule.input.relations
    , Just ps <- mapM isHole rule.input.shapes
    -> do
    let f p = fromJust . Set.lookupMin $ Multi.lookup p rule.origins
    let fromPos p = fromString $ show $ pretty p
    let y = fromTerm rule.output >>= Var . fromPos . f
    return $ lams (fromPos <$> ps) y
  _ -> Nothing

extrs :: [Named Extract] -> (Named (Program Name), [Named [Rule]])
extrs xs = (norm mempty <$> combineFuns (as ++ cs), ds)
  where
    (as, bs) = xs & mapEither \case
      Named name (Fun p) -> Left $ Named name p
      Named name (Rules r) -> Right $ Named name r
    (cs, ds) = bs & mapEither \r -> maybe (Right r) Left $ fromRules r
