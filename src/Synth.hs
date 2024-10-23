{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Synth
  ( Synth
  , SynthC
  , Extract(..)
  , Spec(..)
  , ProofState(..)
  , search
  , tactics
  , applyTactic
  , auto
  , goal
  , extrs
  ) where

import Data.Map qualified as Map
import Data.List qualified as List
import Data.Set qualified as Set
import Data.Maybe (fromJust)

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

import Language.Container.Relation
import Utils
import Data.Map.Multi qualified as Multi
import Tactic
import Tactic.Combinators

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
  pretty p = statements
    [ statements $ pretty <$> p.goals
    , pretty . extrs $ p.extract
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

search :: SynthC a -> Search (Sum Nat) ProofState
search t = evalFresh . execState emptyProofState $ runReader datatypes t

-- TODO: add synthesis options for stuff like this:
-- - whether to abort when out of tactics
-- - whether to allow totality checking on subspecifications
-- - whether to call a bottom-up synthesizer when e.g. only ints remain
tactics :: Synth sig m => [TacticC m Filling] -> m ProofState
tactics [] = get
tactics (t:ts) = next >>= \case
  Nothing -> get
  Just (Named name spec) -> do
    subproblem <- preprocess spec.problem
    applyTactic name subproblem t
    tactics ts

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

applyTactic :: Synth sig m => Name -> Problem -> TacticC m Filling -> m ()
applyTactic name problem m =
  runError (runReader problem m) >>= \case
    Left NotApplicable -> empty
    Left TraceIncomplete -> empty
    Left (Unrealizable _conflict) -> empty
    Right program -> fill name program

fill :: Synth sig m => Name -> Filling -> m ()
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

goal :: Synth sig m => Named Problem -> m ()
goal problem = do
  modify \s -> s { toplevel = problem.name : s.toplevel}
  subgoal problem

subgoal :: Synth sig m => Named Problem -> m ()
subgoal (Named name p) = do
  rules <- runError @Conflict (check =<< preprocess p) >>= \case
    Right r -> return r
    -- TODO: somehow report conflicts
    Left _ -> empty
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
  case (if allowIgnoringInputs then foo else bar) of
    Just _ ->
      let rs' = Named name $ fromJust foo
      in case fromRules rs' of
        Nothing ->
          modify \s -> s { extract = s.extract ++ [Rules <$> rs'] }
        Just f -> do
          modify \s -> s { extract = s.extract ++ [Fun <$> f] }
    _ -> modify \s -> s { unsolved = Queue.insert name s.unsolved }

preprocess :: Synth sig m => Problem -> m Problem
preprocess problem = do
  -- removeUseless $ onArgs flatten problem
  return $ onArgs flatten problem

flatten :: Args -> Args
flatten args = Args inputs args.output
  where
    scope = args.inputs >>= \(Named name arg) -> prjs (Var name, arg)

    prjs :: (Program Void, Arg) -> [(Program Void, Arg)]
    prjs (expr, arg) = case arg.mono of
      Product _ -> concat $ zipWith (\i e -> prjs (Prj i expr, e))
        [0..] (projections arg)
      _ -> [(expr, arg)]

    -- TODO: this is a hack, pretty printing the projections as variables...
    inputs = scope <&> \(x, a) -> Named (fromString . show $ pretty x) a

-- TODO: use relevancy
auto :: Synth sig m => [TacticC m Filling]
auto = repeat $ asum
  [ weigh 2 >> anywhere \v ->
    (introMap v <|> introFilter v) `orElse` (weigh 2 >> fold v)
  , weigh 3 >> anywhere elim
  , weigh 3 >> anywhere2 elimEq
  , weigh 3 >> anywhere2 elimOrd
  , weigh 1 >> introCtr
  , weigh 0 >> introTuple
  , weigh 0 >> anywhere assume
  ]

-- TODO: this is all just for handling extracts

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
