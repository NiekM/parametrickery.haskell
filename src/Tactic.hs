{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

-- | Tactics inspired by refinery.
module Tactic
  ( Tactic
  , TacticC
  , TacticFailure(..)
  , Filling
  , runTactic
  , hole
  , assume
  , introCtr
  , introTuple
  , introMap
  , introFilter
  , elimEq, elimOrd
  , elim
  , fold
  , cata
  ) where

import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map qualified as Map
import Data.Set qualified as Set

import Control.Carrier.Error.Either
import Control.Carrier.Reader
import Control.Effect.Fresh.Named

import Base hiding (fold)
import Language.Container.Morphism
import Language.Expr
import Language.Pretty ()
import Language.Problem
import Language.Relevance
import Language.Type

import Language.Container

data TacticFailure
  = NotApplicable
  | TraceIncomplete
  | Unrealizable Conflict
  deriving stock (Eq, Ord, Show)

instance Pretty TacticFailure where
  pretty = \case
    NotApplicable -> "Not Applicable"
    TraceIncomplete -> "Trace Incomplete"
    Unrealizable conflict -> pretty conflict

type Tactic sig m =
  ( Has (Reader Context) sig m
  , Has (Reader Problem) sig m
  , Has Fresh sig m
  , Has (Throw TacticFailure) sig m
  )

type TacticC m =
  ReaderC Problem (ReaderC Context (ErrorC TacticFailure (FreshC m)))

type Filling = Program (Named Problem)

liftThrow :: Has (Throw e) sig m => (d -> e) -> ErrorC d m a -> m a
liftThrow f m = runError m >>= \case
  Left e -> throwError $ f e
  Right x -> return x

runTactic :: Functor m => Context -> Problem -> TacticC m a ->
  m (Either TacticFailure a)
runTactic ctx problem =
  evalFresh . runError . runReader ctx . runReader problem

getArg :: Tactic sig m => Name -> m Arg
getArg name = do
  inputs <- asks inputArgs
  case find name inputs of
    Nothing -> throwError NotApplicable -- unknown name
    Just arg -> return arg

binds :: Tactic sig m => [Named Arg] -> m Filling -> m Filling
binds args body = do
  renamed <- forM args \(Named name arg) -> nominate name arg
  local (addInputs renamed) do
    let vars = map (.name) renamed
    Lams vars <$> body

checkRealizable :: Tactic sig m => m [Rule]
checkRealizable = do
  problem <- ask @Problem
  liftThrow Unrealizable $ check problem

hole :: Tactic sig m => Name -> m Filling
hole v = do
  _ <- checkRealizable
  name <- freshName v
  elimTuples $ local removeDuplicates $ removeIrrelevant do
    Hole . Named name <$> ask

-- NOTE: computing irrelevance is currently super slow
removeIrrelevant :: Tactic sig m => m Filling -> m Filling
removeIrrelevant cnt = do
  r <- ask >>= relevance
  let
    irrelevantNames = Set.toList $ foldMap (\(signature, _, _) ->
      Set.fromList $ map (.name) . filter ((== Free "_") . (.value)) $ signature.inputs) r.relevance
  local (hide irrelevantNames) cnt

removeDuplicates :: Problem -> Problem
removeDuplicates = onArgs \args ->
  Args (nubOn (.value) args.inputs) args.output
  where nubOn f = map NonEmpty.head . NonEmpty.groupAllWith f

-- NOTE: this seems to work correctly, but fromRules does not work anymore in
-- this different setting
elimTuples :: Tactic sig m => m Filling -> m Filling
elimTuples cnt = do
  args <- asks toArgs
  let
    tuples = args.inputs & filter \arg -> case arg.value.mono of
      Product _ -> True
      _ -> False
    components = tuples >>= \(Named name arg) -> peel (Var name) arg
  xs <- zipWithM nominate (repeat "x") components
  let terms = map (vacuous . fst <$>) xs
  let old = map (.name) tuples
  let new = map (snd <$>) xs
  local (hide old) do
    local (addInputs new) do
      lets terms <$> cnt
  where
    peel :: Program Void -> Arg -> [(Program Void, Arg)]
    peel expr arg = case arg.mono of
      Product _ -> concat $ zipWith (\i e -> peel (Prj i expr) e)
        [0..] (projections arg)
      _ -> [(expr, arg)]

assume :: Tactic sig m => Name -> m Filling
assume name = do
  arg <- getArg name
  out <- asks outputArg
  when (arg /= out) $ throwError NotApplicable -- argument doesn't match spec
  return $ Var name

introTuple :: Tactic sig m => m Filling
introTuple = do
  problem <- ask @Problem
  case problem.signature.output of
    Product _ ->
      tuple <$> forM (projections problem) \p -> local (const p) (hole "_")
    _ -> throwError NotApplicable -- not a tuple

-- TODO: test this properly
introCtr :: Tactic sig m => m Filling
introCtr = do
  problem <- ask @Problem
  case problem.signature.output of
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
          case find c cs of
            Nothing -> error "unknown constructor"
            Just ct -> do
              let goals = projections ct
              es <- forM (zip exampless goals) \(examples, output) -> do
                let signature = problem.signature { output } :: Signature
                local (const Problem { signature, examples }) $ hole "_"
              return . Ctr c $ tuple es
    _ -> throwError NotApplicable -- not a datatype

elimArg :: Tactic sig m => Program Void -> Arg -> m Filling
elimArg expr arg = do
  ctx <- ask @Context
  problem <- ask @Problem
  case split ctx arg problem of
    Nothing -> throwError NotApplicable
    Just m -> do
      -- require all cases to have at least some examples
      when (any (null . (.examples) . snd) m) $ throwError NotApplicable
      arms <- forM m \(a, p) -> do
        local (const p) $ binds [Named "a" a] $ hole "_"
      return $ App (Elim $ Map.assocs arms) (vacuous expr)

elim :: Tactic sig m => Name -> m Filling
elim name = do
  arg <- getArg name
  local (hide [name]) $ elimArg (Var name) arg

-- TODO: we do not have to hide the input list here!
-- we can even pass a non-empty list to f
introMap :: Tactic sig m => Name -> m Filling
introMap name = do
  Arg mono terms <- getArg name
  local (hide [name]) do
    problem <- ask @Problem
    case (mono, problem.signature.output) of
      (Data "List" [t], Data "List" [u]) -> do
        examples <- forM (zip terms problem.examples) \case
          (List inputs, Example scope (List outputs)) -> do
            unless (length inputs == length outputs) $ throwError NotApplicable
            return $ zipWith (\x y -> Example (scope ++ [x]) y) inputs outputs
          _ -> error "Not actually lists."
        x <- freshName "x"
        let Signature constraints context _ = problem.signature
        let signature = Signature constraints (context ++ [Named x t]) u
        let subproblem = Problem signature $ concat examples
        local (const subproblem) do
          f <- hole "f"
          let result = Apps (Var "map") [Lams [x] f, Var name]
          return result
      _ -> throwError NotApplicable

isFilter :: Eq a => [a] -> [a] -> Bool
isFilter xs ys = filter (`elem` ys) xs == ys

-- TODO: we do not have to hide the input list here!
-- we can even pass a non-empty list to f
introFilter :: Tactic sig m => Name -> m Filling
introFilter name = do
  Arg mono terms <- getArg name
  local (hide [name]) do
    problem <- ask @Problem
    case (mono, problem.signature.output) of
      (Data "List" [t], Data "List" [u]) -> do
        when (t /= u) $ throwError NotApplicable
        examples <- forM (zip terms problem.examples) \case
          (List inputs, Example scope (List outputs)) -> do
            unless (isFilter inputs outputs) $ throwError NotApplicable
            return $ List.nub inputs <&> \x ->
              Example (scope ++ [x]) $ Bool $ x `elem` outputs
          _ -> error "Not actually lists."
        x <- freshName "x"
        let
          Signature constraints context _ = problem.signature
          signature =
            Signature constraints (context ++ [Named x t]) (Data "Bool" [])
          subproblem = Problem signature $ concat examples
        local (const subproblem) do
          f <- hole "f"
          let result = Apps (Var "filter") [Lams [x] f, Var name]
          return result
      _ -> throwError NotApplicable

-- TODO: this should add some value in scope that tells the totality checker
-- that some cases are not possible anymore.
elimEq :: Tactic sig m => Name -> Name -> m Filling
elimEq name1 name2 = do
  x <- getArg name1
  y <- getArg name2
  problem <- ask @Problem
  case (x, y) of
    (Arg (Free a) xs, Arg (Free b) ys)
      | a == b
      , Eq a `elem` problem.signature.constraints
      -> do
      let bools = Arg (Data "Bool" []) $ Bool <$> zipWith (==) xs ys
      elimArg (Apps (Var "eq") [Var name1, Var name2]) bools
    _ -> throwError NotApplicable

elimOrd :: Tactic sig m => Name -> Name -> m Filling
elimOrd name1 name2 = do
  x <- getArg name1
  y <- getArg name2
  problem <- ask @Problem
  case (x, y) of
    (Arg (Free a) xs, Arg (Free b) ys)
      | a == b
      , Ord a `elem` problem.signature.constraints
      -> do
      let ords = Arg (Data "Ordering" []) $ Ordering <$> zipWith compare xs ys
      elimArg (Apps (Var "cmp") [Var name1, Var name2]) ords
    _ -> throwError NotApplicable

andThen :: Tactic sig m => m Filling -> m Filling -> m Filling
andThen f g = do
  filling <- f
  join <$> forM filling \(Named _ p) ->
    local (const p) g

fold :: Tactic sig m => Name -> m Filling
fold name = cata name `andThen` do
  elim =<< asks (List.last . variables)

cata :: Tactic sig m => Name -> m Filling
cata name = do
  Arg mono terms <- getArg name
  local (hide [name]) do
    problem <- ask @Problem
    let
      paired = zip terms problem.examples
      restructured = Problem
        { signature = problem.signature
          { inputs = Named name mono : problem.signature.inputs }
        , examples = paired <&> \(i, Example is o) -> Example (i:is) o
        }

    rules <- liftThrow Unrealizable $ check restructured

    let recurse = applyRules rules

    case mono of
      Data d ts -> do
        let baseFunctor = d <> "F"
        ds <- ask @Context
        case find baseFunctor ds.datatypes of
          Nothing -> throwError NotApplicable
          _ -> return ()
        examples <- forM paired \(x, Example ins out) -> do
          e <- poly (Data baseFunctor (ts ++ [Free "r"])) x
          z <- join <$> forM e \case
            ("r", r) -> case recurse (r:ins) of
              Nothing -> throwError TraceIncomplete
              Just q -> return q
            (_, y) -> return y
          return $ Example (ins ++ [z]) out

        r <- freshName "r"
        f <- local (const $ Problem problem.signature
          { inputs = problem.signature.inputs ++
            [ Named r $ Data baseFunctor (ts ++ [problem.signature.output]) ]
          } examples) $ hole "f"

        let result = Apps (Var "cata") [Lams [r] f, Var name]
        return result

      _ -> throwError NotApplicable -- not implemented for all types
