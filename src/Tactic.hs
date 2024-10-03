{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Tactic where

import Data.Map qualified as Map
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty

import Data.Functor.Identity
import Data.Either (rights)

import Control.Effect.Throw
import Control.Effect.Reader
import Control.Effect.Fresh.Named
import Control.Carrier.Error.Either
import Control.Carrier.Reader
import Control.Carrier.State.Strict
import Control.Carrier.Writer.Strict
import Control.Carrier.NonDet.Church

import Debug.Trace

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
    [ pretty spec.problem.signature
    , statements $ map (prettyNamed name) spec.rules
    , parens $ pretty spec.coverage
    -- , pretty goal.relevance
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
  , Has (Error Conflict) sig m
  , Has (State ProofState) sig m
  , Has (Writer [Extract]) sig m
  , Has NonDet sig m
  , MonadPlus m
  )

type TacticC = ReaderC Context (StateC ProofState (WriterC [Extract]
  (ErrorC Conflict (FreshC (NonDetC Identity)))))

runTactic :: TacticC a -> [Either Conflict ([Extract], (ProofState, a))]
runTactic t = run . runNonDetA . evalFresh . runError
  . runWriter . runState mempty $ runReader datatypes t

execTactic :: TacticC a -> [Either Conflict ([Extract], ProofState)]
execTactic t = run . runNonDetA . evalFresh . runError
  . runWriter . execState mempty $ runReader datatypes t

done :: TacticC a -> Maybe [Extract]
done x = List.find bar . map fst . rights $ execTactic x
  where bar = any \case (Fun a) -> a.name == "done"; _ -> False

subgoal :: Tactic sig m => Text -> Problem -> m (Program Text)
subgoal t p = do
  rules <- check p
  name <- freshName t
  c <- coverage p.signature rules
  r <- relevance p
  let sub = Named name $ Spec p rules c r
  modify \s -> s { goals = sub : s.goals }
  case c of
    Total -> tell [Rules name rules]
    _ -> modify \s -> s { unsolved = Queue.insert name s.unsolved }
  return . Hole $ MkHole name

tactic :: Tactic sig m => (Spec -> m (Program Text)) -> m ()
tactic f = next >>= \case
  Nothing -> error "TODO: no more holes"
  Just (Named name spec) -> do
    e <- f spec
    tell [Fun $ Named name e]

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

-- TODO: deal with trace incompleteness: do we just disallow fold?
-- TODO: implement relevancy check
-- TODO: catch errors and throw away unrealizable cases
folds :: Tactic sig m => Nat -> m ProofState
folds 0 = get
folds n = next >>= \case
  Nothing -> tell [Fun (Named "done" $ Hole $ MkHole "!!")] >> get
  Just goal -> do
    catchError @Conflict
      ( do
        let p = goal.value.problem
        x <- msum
          [ foldArgs p
          -- , introCons goal.problem
          , introCtr p
          , tuple p
          , assumption p
          ]
        tell [Fun (Named goal.name x)]
      )
      (const mzero)
    folds (n - 1)

assumption :: Tactic sig m => Problem -> m (Program Text)
assumption problem = do
  (arg, _) <- oneOf $ pickApart problem
  guard $ arg.value == (toArgs problem).output
  return $ Var arg.name

tuple :: Tactic sig m => Problem -> m (Program Text)
tuple problem = case problem.signature.output of
  Product _ -> Tuple <$> forM (projections problem) (subgoal "_")
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
            -- tell [Fun (Named "_" (Ctr c (Hole (MkHole "Text"))))]
            es <- forM (zip exampless goals) \(examples, output) -> do
              let signature = problem.signature { output } :: Signature
              subgoal "_" Problem { signature, examples }
            return . Ctr c $ Tuple es
  _ -> mzero

introCons :: Tactic sig m => Problem -> m ()
introCons problem = case problem.signature.output of
  Data "List" [t] -> do
    exs <- forM problem.examples \example -> case example.output of
      Cons x xs -> return
        ( example { output = x  } :: Example
        , example { output = xs } :: Example
        )
      _ -> mzero
    let (hd, tl) = unzip exs
    _ <- subgoal "h" Problem
      { signature = problem.signature { output = t }
      , examples = hd
      }
    _ <- subgoal "t" Problem
      { signature = problem.signature
      , examples = tl
      }
    return ()
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
      (fmap \(Arg ty ys) -> Arg ty (x:ys))
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

foldArgs :: Tactic sig m => Problem -> m (Program Text)
foldArgs problem = do
  (arg, prob) <- oneOf $ pickApart problem
  fold arg prob

fold :: Tactic sig m => Named Arg -> Problem -> m (Program Text)
fold (Named name (Arg ty terms)) problem = do

  let paired = zip terms problem.examples
  rules <- check Problem
    { signature = problem.signature
      { inputs = Named name ty : problem.signature.inputs }
    , examples = paired <&> \(i, Example is o) -> Example (i:is) o
    }
  let recurse = applyRules rules

  case ty of
    Data "List" [t] -> do 
      constrs <- forM paired \case
        (Nil, ex) -> return $ Left ex
        (Cons y ys, Example ins out) ->
          case recurse (ys:ins) of
            Nothing -> do
              traceM $ show (pretty name) ++ ": trace incomplete"
              mzero
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
      return $ apps (Var "fold") [f, e]

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
      return $ apps (Var "fold") [f, e]

    _ -> mzero
