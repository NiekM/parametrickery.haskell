{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

-- | Tactics inspired by refinery.
module Tactic where

import Data.Map qualified as Map
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty

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

data TacticFailure
  = UnexpectedType Mono
  | NotApplicable
  | TraceIncompleteness
  deriving stock (Eq, Ord, Show)

type Tactic sig m =
  ( Has (Reader Context) sig m
  , Has Fresh sig m
  , Has (Error Conflict) sig m
  , Has (Error TacticFailure) sig m
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

nominate :: Has Fresh sig m => Name -> a -> m (Named a)
nominate name x = do
  a <- freshName name
  return $ Named a x

applyTactic :: Synth sig m => Name ->
  ErrorC Conflict (ErrorC TacticFailure m) (Program (Named Problem)) -> m ()
applyTactic name m = runError (runError m) >>= \case
  Left _tacticFailure -> mzero
  Right (Left _conflict) -> mzero
  Right (Right p) -> Tactic.fill name p

names :: Traversable f => f (Named v) -> (Map Name v, f Name)
names = traverse \(Named name x) -> (Map.singleton name x, name)

fill :: Synth sig m => Name -> Program (Named Problem) -> m ()
fill h p = do
  st <- get @ProofState
  case st.goals & List.find \x -> x.name == h of
    Nothing -> error "Unknown hole"
    Just (Named name spec) -> do
      let (new, p'') = names p
      let vars = (.name) <$> spec.problem.signature.inputs
      modify \s -> s { extract =
        s.extract ++ [Named name . Fun $ lams vars p''] }
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

    inputs = scope <&> \(x, a) -> Named (fromString . show $ pretty x) a

  in Args inputs args.output

-- TODO: deal with trace incompleteness: do we just disallow fold?
-- TODO: implement relevancy check
auto :: Synth sig m => Nat -> m ProofState
auto 0 = mzero
auto n = next >>= \case
  Nothing -> get
  Just spec -> do
    let subproblem = flatten spec.value.problem
    _ <- msum
      [ weigh 3 >> anywhere (\a -> applyTactic spec.name . cata a) subproblem
       -- TODO: should we always perform introTuple after introCtr?
      , weigh 1 >> applyTactic spec.name (introCtr subproblem)
      , weigh 0 >> applyTactic spec.name (introTuple subproblem)
      , weigh 0 >> anywhere (\a -> applyTactic spec.name . assume a) subproblem
      ]
    auto (n - 1)

assume :: Tactic sig m => Named Arg -> Problem -> m (Program (Named Problem))
assume arg problem
  | arg.value == (toArgs problem).output = return $ Var arg.name
  | otherwise = throwError NotApplicable -- argument doesn't match spec

introTuple :: Tactic sig m => Problem -> m (Program (Named Problem))
introTuple problem = case problem.signature.output of
  Product _ -> do
    let vars = Var <$> variables problem
    es <- forM (projections problem) (hole "_")
    return . Tuple $ es <&> \e -> apps e vars
  _ -> throwError NotApplicable -- not a tuple

-- TODO: test this properly
introCtr :: Tactic sig m => Problem -> m (Program (Named Problem))
introCtr problem = case problem.signature.output of
  Data d ts -> do
    cs <- asks $ getConstructors d ts
    -- TODO: getConstructor that returns the fields of one specific ctr
    exs <- forM problem.examples \example -> case example.output of
      Ctr c e -> (c,) <$> forM (projections e) \x ->
        return (example { output = x } :: Example)
      _ -> throwError NotApplicable -- output not a constructor
    case NonEmpty.groupAllWith fst exs of
      [] -> throwError NotApplicable -- no examples
      (_:_:_) -> throwError NotApplicable -- not all examples agree
      [xs] -> do
        let c = fst $ NonEmpty.head xs
        let exampless = List.transpose $ snd <$> NonEmpty.toList xs
        case List.find (\ct -> ct.name == c) cs of
          Nothing -> error "unknown constructor"
          Just ct -> do
            let goals = projections ct.field
            es <- forM (zip exampless goals) \(examples, output) -> do
              let signature = problem.signature { output } :: Signature
              hole "_" $ Problem { signature, examples }
            let vars = Var <$> variables problem
            return . Ctr c $ Tuple (es <&> \e -> apps e vars)
  _ -> throwError NotApplicable -- not a datatype

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

-- introMap :: Tactic sig m => Named Arg -> Problem -> m ()
-- introMap (Named _ (Arg ty terms)) problem =
--   case (ty, problem.signature.output) of
--     (Data "List" [t], Data "List" [u]) -> do
--       examples <- forM (zip terms problem.examples) \case
--         (List inputs, Example scope (List outputs)) -> do
--           guard $ length inputs == length outputs
--           return $ zipWith (\x y -> Example (scope ++ [x]) y) inputs outputs
--         _ -> error "Not actually lists."
--       x <- freshName "x"
--       let Signature constraints context _ = problem.signature
--       let signature = Signature constraints (context ++ [Named x t]) u
--       _ <- subgoal "f" $ Problem signature (concat examples)
--       return ()
--     _ -> mzero

anywhere :: Synth sig m => (Named Arg -> Problem -> m a) -> Problem -> m a
anywhere f problem = do
  (arg, prob) <- oneOf $ pickApart problem
  f arg prob

hole :: Tactic sig m => Name -> Problem -> m (Program (Named Problem))
hole t problem = do
  name <- freshName t
  return . Hole . MkHole $ Named name problem

cata :: Tactic sig m => Named Arg -> Problem -> m (Program (Named Problem))
cata (Named name (Arg ty terms)) problem = do

  let
    paired = zip terms problem.examples
    restructured = Problem
      { signature = problem.signature
        { inputs = Named name ty : problem.signature.inputs }
      , examples = paired <&> \(i, Example is o) -> Example (i:is) o
      }

  rules <- check restructured

  let recurse = applyRules rules

  case ty of
    Data "List" [t] -> do 
      constrs <- forM paired \case
        (Nil, ex) -> return $ Left ex
        (Cons y ys, Example ins out) ->
          case recurse (ys:ins) of
            -- TODO: perhaps we want more explicit results\errors from
            -- tactics, such as an error of trace completeness, which can then
            -- be caught by the synthesis loop.
            Nothing -> throwError TraceIncompleteness
            Just r -> return . Right $ Example (ins ++ [y, r]) out
        _ -> error "Expected a list!"

      let (nil, cons) = partitionEithers constrs

      e <- hole "e" $ problem { examples = nil }

      x <- freshName "x"
      r <- freshName "r"
      f <- hole "f" $ Problem problem.signature
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
            _ -> throwError TraceIncompleteness
        _ -> error "Expected a tree!"

      let (leaf, node) = partitionEithers constrs

      y <- freshName "y"
      e <- hole "e" $ Problem problem.signature
        { inputs = problem.signature.inputs ++ [ Named y u ] } leaf

      l <- freshName "l"
      x <- freshName "x"
      r <- freshName "r"
      f <- hole "f" $ Problem problem.signature
        { inputs = problem.signature.inputs ++
          [ Named l problem.signature.output
          , Named x t
          , Named r problem.signature.output
          ]
        } node
      let vars = Var <$> variables problem
      return $ apps (Var "fold") [apps f vars, apps e vars, Var name]

    _ -> throwError $ UnexpectedType ty

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
