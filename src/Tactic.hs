{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

-- | Tactics inspired by refinery.
module Tactic where

import Data.Text qualified as Text
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty

import Data.Functor.Identity

import Control.Effect.Throw
import Control.Effect.Reader
import Control.Effect.Fresh.Named
import Control.Effect.Weight
import Control.Carrier.Error.Either
import Control.Carrier.Reader
import Control.Carrier.State.Strict
import Control.Carrier.Writer.Strict
import Control.Carrier.NonDet.Church

import Data.PQueue.Max (MaxQueue)
import Data.PQueue.Max qualified as Queue

import Control.Monad.Search
import Control.Effect.Search ()

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
pickApart p@(Problem Signature { inputs } _) =
  zipWith const [0..] inputs & mapMaybe (`pickArg` p)

addArgs :: [Named Arg] -> Problem -> Problem
addArgs [] p = p
addArgs args Problem { signature, examples } =
  Problem
    { signature = signature { inputs = signature.inputs ++ types }
    , examples = zipWith addInputs terms examples
    }
  where
    types = args <&> fmap (.mono)
    terms = List.transpose $ map (.value.terms) args
    addInputs :: [Value] -> Example -> Example
    addInputs new (Example inputs output) = Example (inputs ++ new) output

data Extract
  = Fun (Named (Program Text))
  | Rules Text [Rule]
  deriving stock (Eq, Ord, Show)

instance Pretty Extract where
  pretty = \case
    Fun p -> pretty p
    Rules t r -> statements $ prettyNamed t <$> r

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
  { goals    :: [Named Spec]
  , unsolved :: MaxQueue Text
  } deriving stock (Eq, Ord, Show)

instance Semigroup ProofState where
  a <> b = ProofState (a.goals <> b.goals) (a.unsolved <> b.unsolved)

instance Monoid ProofState where
  mempty = ProofState [] mempty

instance Pretty ProofState where
  pretty p = statements $ pretty <$> p.goals

type Tactic sig m =
  ( Has (Reader Context) sig m
  , Has Fresh sig m
  , Has (State ProofState) sig m
  , Has (Writer [Extract]) sig m
  , Has Weight sig m
  , Has NonDet sig m
  , MonadPlus m
  )

type SearchC = ReaderC Context (StateC ProofState (WriterC [Extract]
  (FreshC (Search (Sum Nat)))))

-- TODO: can we get rid of the Either Conflict? Since these should all be
-- caught, right? Perhaps Tactic should not contain Error Conflict, and the
-- function tactic allows Conflicts locally but then turns them into Empty.
search :: SearchC a -> Search (Sum Nat) ([Extract], ProofState)
search t = evalFresh . runWriter . execState mempty $ runReader datatypes t

type TacticC = ReaderC Context (StateC ProofState (WriterC [Extract]
  (FreshC (IgnoreC (NonDetC Identity)))))

execTactic :: TacticC a -> [([Extract], ProofState)]
execTactic t = run . runNonDetA . ignoreWeight . evalFresh .
  runWriter . execState mempty $ runReader datatypes t

subgoal :: Tactic sig m => Text -> Problem -> m (Program Text)
subgoal t p = do
  rules <- runError @Conflict (check p) >>= either (const mzero) return
  name <- freshName t
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
    Just rs -> tell [Rules name rs]
    _ -> modify \s -> s { unsolved = Queue.insert name s.unsolved }
  return . Hole $ MkHole name

-- tactic :: Tactic sig m => (Spec -> m (Program Text)) -> m ()
-- tactic f = next >>= \case
--   Nothing -> error "TODO: no more holes"
--   Just (Named name spec) -> do
--     e <- f spec
--     tell [Fun $ Named name e]

next :: Tactic sig m => m (Maybe (Named Spec))
next = do
  gs <- get @ProofState
  case Queue.maxView gs.unsolved of
    Nothing -> return Nothing
    Just (x, xs) -> case List.find (\g -> g.name == x) gs.goals of
      Nothing -> error "unknown goal"
      Just g -> do
        modify \s -> s { unsolved = xs }
        return $ Just g

flatten :: Problem -> Problem
flatten = onArgs \args ->
  let
    scope = args.inputs >>= \(Named name arg) -> split (Var name, arg)

    split :: (Program Void, Arg) -> [(Program Void, Arg)]
    split (expr, arg) = case arg.mono of
      Product _ -> concat $ zipWith (\i e -> split (Prj i expr, e))
        [0..] (projections arg)
      _ -> [(expr, arg)]

    inputs = scope <&> \(x, a) -> Named (Text.pack . show $ pretty x) a

  in Args inputs args.output

-- TODO: deal with trace incompleteness: do we just disallow fold?
-- TODO: implement relevancy check
-- TODO: catch errors and throw away unrealizable cases
auto :: Tactic sig m => Nat -> m ProofState
auto 0 = mzero
auto n = next >>= \case
  Nothing -> get
  Just goal -> do
    let subproblem = flatten goal.value.problem
    x <- msum
      [ weigh 3 >> anywhere cata subproblem
       -- TODO: should we always perform introTuple after introCtr?
      , weigh 1 >> introCtr subproblem
      , weigh 0 >> introTuple subproblem
      , weigh 0 >> anywhere assume subproblem
      ]
    let vars = (.name) <$> goal.value.problem.signature.inputs
    tell [Fun (Named goal.name (lams vars x))]
    auto (n - 1)

assume :: Tactic sig m => Named Arg -> Problem -> m (Program Text)
assume arg problem = do
  guard $ arg.value == (toArgs problem).output
  return $ Var arg.name

introTuple :: Tactic sig m => Problem -> m (Program Text)
introTuple problem = case problem.signature.output of
  Product _ -> do
    let vars = Var <$> variables problem
    es <- forM (projections problem) (subgoal "_")
    return . Tuple $ es <&> \e -> apps e vars
  _ -> mzero

-- TODO: test this properly
introCtr :: Tactic sig m => Problem -> m (Program Text)
introCtr problem = case problem.signature.output of
  Data d ts -> do
    cs <- asks $ getConstructors d ts
    -- TODO: getConstructor that returns the fields of one specific ctr
    exs <- forM problem.examples \example -> case example.output of
      Ctr c e -> (c,) <$> forM (projections e) \x ->
        return (example { output = x } :: Example)
      _ -> mzero
    case NonEmpty.groupAllWith fst exs of
      [] -> mzero --error "no examples"
      (_:_:_) -> mzero -- Not all examples agree.
      [xs] -> do
        let c = fst $ NonEmpty.head xs
        let exampless = List.transpose $ snd <$> NonEmpty.toList xs
        case List.find (\ct -> ct.name == c) cs of
          Nothing -> error "unknown constructor"
          Just ct -> do
            let goals = projections ct.field
            es <- forM (zip exampless goals) \(examples, output) -> do
              let signature = problem.signature { output } :: Signature
              subgoal "_" Problem { signature, examples }
            let vars = Var <$> variables problem
            return . Ctr c $ Tuple (es <&> \e -> apps e vars)
  _ -> mzero

-- caseSplit :: Has (Reader Context) sig m =>
--   Named Arg -> Problem -> m (Map Text (Named Arg, Problem))
-- caseSplit (Named name (Arg (Data d ts) terms)) prob = do
--   cs <- asks $ getConstructors d ts
--   let
--     e = Map.fromList $ cs <&> \c ->
--       ( c.name
--       , ( Named (name <> "_" <> c.name) (Arg c.field [])
--         , Problem prob.signature []
--         )
--       )
--     f m (Ctr c x, ex) = Map.adjust (bimap
--       (fmap \(Arg ty ys) -> Arg ty (x:ys))
--       (\(Problem sig exs) -> Problem sig (ex:exs))) c m
--     f _ _ = error "Not a constructor"
--   return $ List.foldl' f e (zip terms prob.examples)
-- caseSplit _ _ = error "Not a datatype"

-- split :: Tactic sig m => Named Arg -> Problem -> m ()
-- split arg problem = do
--   m <- caseSplit arg problem
--   forM_ (Map.elems m) \(Named v a, p) -> do
--     as <- forM (projections a) \x -> do
--       name <- freshName v
--       return $ Named name x
--     subgoal v $ addArgs as p

introMap :: Tactic sig m => Named Arg -> Problem -> m ()
introMap (Named _ (Arg ty terms)) problem =
  case (ty, problem.signature.output) of
    (Data "List" [t], Data "List" [u]) -> do
      examples <- forM (zip terms problem.examples) \case
        (List inputs, Example scope (List outputs)) -> do
          guard $ length inputs == length outputs
          return $ zipWith (\x y -> Example (scope ++ [x]) y) inputs outputs
        _ -> error "Not actually lists."
      x <- freshName "x"
      let Signature constraints context _ = problem.signature
      let signature = Signature constraints (context ++ [Named x t]) u
      _ <- subgoal "f" $ Problem signature (concat examples)
      return ()
    _ -> mzero

anywhere :: Tactic sig m => (Named Arg -> Problem -> m a) -> Problem -> m a
anywhere f problem = do
  (arg, prob) <- oneOf $ pickApart problem
  f arg prob

cata :: Tactic sig m => Named Arg -> Problem -> m (Program Text)
cata (Named name (Arg ty terms)) problem = do

  let
    paired = zip terms problem.examples
    restructured = Problem
      { signature = problem.signature
        { inputs = Named name ty : problem.signature.inputs }
      , examples = paired <&> \(i, Example is o) -> Example (i:is) o
      }

  -- TODO: recapture conflict info. maybe tactics should return a bit more:
  -- - did they apply?
  -- - if so, did they succeed?
  -- we can use this info for deciding which tactics to try next
  rules <- runError @Conflict (check restructured) >>=
    either (const mzero) return

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

      e <- subgoal "e" $ problem { examples = nil }

      x <- freshName "x"
      r <- freshName "r"
      f <- subgoal "f" $ Problem problem.signature
        { inputs = problem.signature.inputs ++
          [ Named x t
          , Named r problem.signature.output
          ]
        } cons
      let vars = Var <$> variables problem
      return $ apps (Var "fold") [apps f vars, apps e vars, Var name]

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
      e <- subgoal "e" $ Problem problem.signature
        { inputs = problem.signature.inputs ++ [ Named y u ] } leaf

      l <- freshName "l"
      x <- freshName "x"
      r <- freshName "r"
      f <- subgoal "f" $ Problem problem.signature
        { inputs = problem.signature.inputs ++
          [ Named l problem.signature.output
          , Named x t
          , Named r problem.signature.output
          ]
        } node
      let vars = Var <$> variables problem
      return $ apps (Var "fold") [apps f vars, apps e vars, Var name]

    _ -> mzero
