{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

-- | Tactics inspired by refinery.
module Tactic
  ( Tactic
  , TacticC
  , TacticFailure(..)
  , Filling
  , runTactic
  , assume
  , introCtr
  , introTuple
  , introMap
  , introFilter
  , elimEq, elimOrd
  , elim
  , fold
  ) where

import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map qualified as Map
import Prelude hiding (succ)

import Control.Carrier.Error.Either
import Control.Carrier.Reader
import Control.Effect.Fresh.Named

import Base
import Language.Container.Morphism
import Language.Expr
import Language.Pretty ()
import Language.Problem
import Language.Type

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

runTactic :: Functor m => Problem -> TacticC m a -> m (Either TacticFailure a)
runTactic problem =
  evalFresh . runError . runReader datatypes . runReader problem

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
    lams vars <$> body

hole :: Tactic sig m => Name -> m Filling
hole v = do
  name <- freshName v
  elimTuples $ local removeDuplicates do
    Hole . MkHole . Named name <$> ask

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
  let inputs' = map (snd <$>) xs
  local (foldr (\x -> (hide x.name .)) id tuples) do
    local (addInputs inputs') do
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
        let letters = fromString . pure <$> ['a' ..]
        let xs = zipWith Named letters (projections a)
        local (const p) $ binds xs $ hole "_"
      return $ App (Elim $ Map.assocs arms) (vacuous expr)

elim :: Tactic sig m => Name -> m Filling
elim name = do
  arg <- getArg name
  local (hide name) $ elimArg (Var name) arg

-- TODO: we do not have to hide the input list here!
-- we can even pass a non-empty list to f
introMap :: Tactic sig m => Name -> m Filling
introMap name = do
  Arg mono terms <- getArg name
  local (hide name) do
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
        _ <- liftThrow Unrealizable $ check subproblem
        local (const subproblem) do
          f <- hole "f"
          let result = apps (Var "map") [lams [x] f, Var name]
          return result
      _ -> throwError NotApplicable

bool :: Bool -> Expr l h
bool False = Ctr "False" Unit
bool True  = Ctr "True"  Unit

ordering :: Ordering -> Expr l h
ordering LT = Ctr "LT" Unit
ordering EQ = Ctr "EQ" Unit
ordering GT = Ctr "GT" Unit

isFilter :: Eq a => [a] -> [a] -> Bool
isFilter xs ys = filter (`elem` ys) xs == ys

-- TODO: we do not have to hide the input list here!
-- we can even pass a non-empty list to f
introFilter :: Tactic sig m => Name -> m Filling
introFilter name = do
  Arg mono terms <- getArg name
  local (hide name) do
    problem <- ask @Problem
    case (mono, problem.signature.output) of
      (Data "List" [t], Data "List" [u]) -> do
        when (t /= u) $ throwError NotApplicable
        examples <- forM (zip terms problem.examples) \case
          (List inputs, Example scope (List outputs)) -> do
            unless (isFilter inputs outputs) $ throwError NotApplicable
            return $ List.nub inputs <&> \x ->
              Example (scope ++ [x]) $ bool $ x `elem` outputs
          _ -> error "Not actually lists."
        x <- freshName "x"
        let
          Signature constraints context _ = problem.signature
          signature =
            Signature constraints (context ++ [Named x t]) (Data "Bool" [])
          subproblem = Problem signature $ concat examples
        _ <- liftThrow Unrealizable $ check subproblem
        local (const subproblem) do
          f <- hole "f"
          let result = apps (Var "filter") [lams [x] f, Var name]
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
      let bools = Arg (Data "Bool" []) $ bool <$> zipWith (==) xs ys
      elimArg (apps (Var "eq") [Var name1, Var name2]) bools
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
      let ords = Arg (Data "Ordering" []) $ ordering <$> zipWith compare xs ys
      elimArg (apps (Var "cmp") [Var name1, Var name2]) ords
    _ -> throwError NotApplicable

fold :: Tactic sig m => Name -> m Filling
fold name = do
  Arg mono terms <- getArg name
  local (hide name) do
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
      Data "List" [t] -> do 
        constrs <- forM paired \case
          (Nil, ex) -> return $ Left ex
          (Cons y ys, Example ins out) ->
            case recurse (ys:ins) of
              Nothing -> throwError TraceIncomplete
              Just r -> return . Right $ Example (ins ++ [y, r]) out
          _ -> error "Expected a list!"

        let (nil, cons) = partitionEithers constrs

        e <- local (const $ problem { examples = nil }) $ hole "e"

        x <- freshName "x"
        r <- freshName "r"
        f <- local (const $ Problem problem.signature
          { inputs = problem.signature.inputs ++
            [ Named x t
            , Named r problem.signature.output
            ]
          } cons) $ hole "f"

        let result = apps (Var "fold") [lams [x, r] f, e, Var name]
        forM_ result \subproblem ->
          liftThrow Unrealizable $ check subproblem.value
        return result

      Data "Tree" [t, u] -> do
        constrs <- forM paired \case
          (Ctr "Leaf" x, Example ins out) -> return . Left $
            Example (ins ++ [x]) out
          (Ctr "Node" (Tuple [l, x, r]), Example ins out) ->
            case (recurse (l:ins), recurse (r:ins)) of
              (Just left, Just right) -> return . Right $
                Example (ins ++ [left, x, right]) out
              _ -> throwError TraceIncomplete
          _ -> error "Expected a tree!"

        let (leaf, node) = partitionEithers constrs

        y <- freshName "y"
        e <- local (const $ Problem problem.signature
          { inputs = problem.signature.inputs ++ [ Named y u ] } leaf) $ hole "e"

        l <- freshName "l"
        x <- freshName "x"
        r <- freshName "r"
        f <- local (const $ Problem problem.signature
          { inputs = problem.signature.inputs ++
            [ Named l problem.signature.output
            , Named x t
            , Named r problem.signature.output
            ]
          } node) $ hole "f"

        let result = apps (Var "fold") [lams [l, x, r] f, e, Var name]
        forM_ result \subproblem ->
          liftThrow Unrealizable $ check subproblem.value
        return result

      Data "Nat" [] -> do
        constrs <- forM paired \case
          (Ctr "Zero" _, ex) -> return $ Left ex
          (Ctr "Succ" n, Example ins out) ->
            case recurse (n:ins) of
              Nothing -> throwError TraceIncomplete
              Just r -> return . Right $ Example (ins ++ [r]) out
          _ -> error "Expected a nat!"

        let (zero, succ) = partitionEithers constrs

        e <- local (const $ problem { examples = zero }) $ hole "e"

        r <- freshName "r"
        f <- local (const $ Problem problem.signature
          { inputs = problem.signature.inputs ++
            [ Named r problem.signature.output ]
          } succ) $ hole "f"

        let result = apps (Var "fold") [lams [r] f, e, Var name]
        forM_ result \subproblem ->
          liftThrow Unrealizable $ check subproblem.value
        return result

      _ -> throwError NotApplicable -- not implemented for all types
