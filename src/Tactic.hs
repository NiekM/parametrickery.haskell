{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

-- | Tactics inspired by refinery.
module Tactic
  ( Tactic
  , Settings(..)
  , defaultSettings
  , TacticFailure(..)
  , notApplicable
  , Filling
  , getArg
  , none
  , hole
  , andThen, (>>>)
  , focus, (>>*)
  , assume
  , introCtr
  , introTuple
  , elimArg
  , elim
  , liftThrow
  ) where

import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map qualified as Map
import Data.Set qualified as Set

import Control.Carrier.Error.Either
import Control.Carrier.Reader
import Control.Effect.Fresh.Named
import Control.Carrier.State.Strict

import Base hiding (fold)
import Language.Container.Morphism
import Language.Expr
import Language.Pretty ()
import Language.Problem
import Language.Relevance
import Language.Type

import Utils

-- TODO: split into multiple files

data Settings = Settings
  { removeDuplicates :: Bool
  , removeIrrelevant :: Bool
  } deriving (Eq, Ord, Show)

defaultSettings :: Settings
defaultSettings = Settings
  { removeDuplicates = True
  , removeIrrelevant = False
  }

data TacticFailure
  = NotApplicable Text
  | TraceIncomplete
  | PropagationError Text
  | Unrealizable Conflict
  deriving stock (Eq, Ord, Show)

instance Pretty TacticFailure where
  pretty = \case
    NotApplicable t -> "Not Applicable:" <+> pretty t
    TraceIncomplete -> "Trace Incomplete"
    PropagationError t -> "Propagation Failed:" <+> pretty t
    Unrealizable conflict -> pretty conflict

type Tactic sig m =
  ( Has (Reader DataContext) sig m
  , Has (Reader Settings) sig m
  , Has (Reader Problem) sig m
  , Has Fresh sig m
  , Has (Throw TacticFailure) sig m
  )

type Filling = Program Problem

notApplicable :: Has (Throw TacticFailure) sig m => Text -> m a
notApplicable = throwError . NotApplicable

liftThrow :: Has (Throw e) sig m => (d -> e) -> ErrorC d m a -> m a
liftThrow f m = runError m >>= \case
  Left e -> throwError $ f e
  Right x -> return x

getArg :: Tactic sig m => Name -> m Arg
getArg name = do
  inputs <- asks inputArgs
  case find name inputs of
    Nothing -> notApplicable $ "unknown name " <> name.getName
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

tryRealizable :: Tactic sig m => m Filling -> m Filling
tryRealizable cnt = do
  rules <- checkRealizable
  local (reconstruct rules) cnt

none :: Tactic sig m => m Filling
none = Hole <$> ask

hole :: Tactic sig m => Bool -> m Filling
hole recalculate = do
  settings :: Settings <- ask
  foldr (.) id
    [ elimTuples
    , applyWhen settings.removeDuplicates $ local removeIdenticalInputs
    , applyWhen settings.removeIrrelevant removeIrrelevant
    , applyWhen recalculate tryRealizable
    ] none

-- NOTE: computing irrelevance is currently super slow
removeIrrelevant :: Tactic sig m => m Filling -> m Filling
removeIrrelevant cnt = do
  r <- ask >>= relevance
  let
    irrelevantNames = Set.toList $ foldMap (\(signature, _, _) ->
      Set.fromList $ map (.name) . filter ((== Free "_") . (.value)) $ signature.inputs) r.relevance
  local (hide irrelevantNames) cnt

removeIdenticalInputs :: Problem -> Problem
removeIdenticalInputs = onArgs \args ->
  Args (nubOn (.value) args.inputs) args.output

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
  when (arg /= out) $ notApplicable "argument doesn't match spec"
  return $ Var name

introTuple :: Tactic sig m => m Filling
introTuple = do
  problem <- ask @Problem
  case problem.signature.output of
    Product _ ->
      tuple <$> forM (projections problem) \p ->
        local (const p) (hole False)
    _ -> notApplicable "goal is not a tuple"

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
        _ -> notApplicable "output not a constructor"
      case NonEmpty.groupAllWith fst exs of
        [] -> notApplicable "no examples"
        (_:_:_) -> notApplicable "not all examples agree"
        [xs] -> do
          let c = fst $ NonEmpty.head xs
          let exampless = List.transpose $ snd <$> NonEmpty.toList xs
          case find c cs of
            Nothing -> error "unknown constructor"
            Just ct -> do
              let goals = projections ct
              es <- forM (zip exampless goals) \(examples, output) -> do
                let signature = problem.signature { output } :: Signature
                local (const Problem { signature, examples }) $ hole False
              return . Ctr c $ tuple es
    _ -> notApplicable "goal is not a datatype"

elimArg :: Tactic sig m => Program Void -> Arg -> m Filling
elimArg expr arg = do
  ctx <- ask @DataContext
  problem <- ask @Problem
  case split ctx arg problem of
    Left e -> notApplicable $ "elim: " <> e
    Right m -> do
      -- require all cases to have at least some examples
      -- TODO: this tactic should not be disallowed when examples are missing, but during synthesis we should have an option to disallow it.
      -- maybe as an argoment to this function? This also disallows e.g. elimOrd when not all cases are present.
      when (any (null . (.examples) . snd) m) $ notApplicable "not all cases have examples"
      arms <- forM m \(a, p) -> do
        local (const p) $ binds [Named "x" a] $ hole False
      return $ App (Elim $ Map.assocs arms) (vacuous expr)

elim :: Tactic sig m => Name -> m Filling
elim name = do
  arg <- getArg name
  local (hide [name]) $ elimArg (Var name) arg

andThen, (>>>) :: Tactic sig m => m Filling -> m Filling -> m Filling
andThen f g = do
  filling <- f
  join <$> forM filling \p -> local (const p) g
(>>>) = andThen

enumerate :: Traversable t => t a -> t (Nat, a)
enumerate t = run $ evalState @Nat 0 do
  t & traverse \x -> do
    n <- get
    put (n + 1)
    return (n, x)

focus :: Tactic sig m => Nat -> m Filling -> m Filling -> m Filling
focus n f g = f >>* (replicate (fromIntegral n) none ++ [g])

(>>*) :: Tactic sig m => m Filling -> [m Filling] -> m Filling
(>>*) f gs = do
  filling <- f
  let numbered = enumerate filling
  join <$> forM numbered \(n, p) ->
    local (const p) case gs List.!? (fromIntegral n) of
      Nothing -> none
      Just g -> g

