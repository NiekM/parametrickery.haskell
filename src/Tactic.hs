{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

-- | Tactics inspired by refinery.
module Tactic
  ( Tactic
  , TacticFailure(..)
  , assume
  , introCtr
  , introTuple
  , introMap
  , elim
  , fold
  ) where

import Data.Map qualified as Map
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty

import Control.Effect.Throw
import Control.Effect.Reader
import Control.Effect.Fresh.Named
import Control.Carrier.Error.Either

import Base
import Language.Type
import Language.Expr
import Language.Problem
import Language.Container.Morphism

data TacticFailure
  = NotApplicable
  | TraceIncomplete
  | Unrealizable Conflict
  deriving stock (Eq, Ord, Show)

type Tactic sig m =
  ( Has (Reader Context) sig m
  , Has (Reader Problem) sig m
  , Has Fresh sig m
  , Has (Throw TacticFailure) sig m
  )

liftThrow :: Has (Throw e) sig m => (d -> e) -> ErrorC d m a -> m a
liftThrow f m = runError m >>= \case
  Left e -> throwError $ f e
  Right x -> return x

getArg :: Tactic sig m => Name -> m Arg
getArg name = do
  inputs <- asks inputArgs
  case find name inputs of
    Nothing -> throwError NotApplicable -- unknown name
    Just arg -> return arg

hole :: Tactic sig m => Name -> Problem -> m (Program (Named Problem))
hole t problem = do
  name <- freshName t
  return . Hole . MkHole $ Named name problem

assume :: Tactic sig m => Name -> m (Program (Named Problem))
assume name = do
  arg <- getArg name
  out <- asks outputArg
  when (arg /= out) $ throwError NotApplicable -- argument doesn't match spec
  return $ Var name

introTuple :: Tactic sig m => m (Program (Named Problem))
introTuple = do
  problem <- ask @Problem
  case problem.signature.output of
    Product _ -> do
      let vars = Var <$> variables problem
      es <- forM (projections problem) (hole "_")
      return . tuple $ es <&> \e -> apps e vars
    _ -> throwError NotApplicable -- not a tuple

-- TODO: test this properly
introCtr :: Tactic sig m => m (Program (Named Problem))
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
                hole "_" $ Problem { signature, examples }
              let vars = Var <$> variables problem
              return . Ctr c $ tuple (es <&> \e -> apps e vars)
    _ -> throwError NotApplicable -- not a datatype

elim :: Tactic sig m => Name -> m (Program (Named Problem))
elim name = do
  arg <- getArg name
  local (hide name) do
    ctx <- ask @Context
    problem <- ask @Problem
    case split ctx arg problem of
      Nothing -> throwError NotApplicable
      Just m -> do
        let vars = Var <$> variables problem
        arms <- forM (Map.elems m) \(a, p) -> do
          let letters = fromString . pure <$> ['a' ..]
          xs <- zipWithM nominate letters (projections a)
          h <- hole "_" (addInputs xs p)
          return $ apps h vars
        return $ apps (Var "elim") (arms ++ [Var name])

introMap :: Tactic sig m => Name -> m (Program (Named Problem))
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
        let vars = Var <$> variables problem
        let subproblem = Problem signature $ concat examples
        _ <- liftThrow Unrealizable $ check subproblem
        f <- hole "f" subproblem
        let result = apps (Var "map") [apps f vars, Var name]
        return result
      _ -> throwError NotApplicable

fold :: Tactic sig m => Name -> m (Program (Named Problem))
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
      vars = Var <$> variables problem

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

        e <- hole "e" $ problem { examples = nil }

        x <- freshName "x"
        r <- freshName "r"
        f <- hole "f" $ Problem problem.signature
          { inputs = problem.signature.inputs ++
            [ Named x t
            , Named r problem.signature.output
            ]
          } cons

        let result = apps (Var "fold") [apps f vars, apps e vars, Var name]
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

        let result = apps (Var "fold") [apps f vars, apps e vars, Var name]
        forM_ result \subproblem ->
          liftThrow Unrealizable $ check subproblem.value
        return result

      _ -> throwError NotApplicable -- not implemented for all types
