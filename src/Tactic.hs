{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

-- | Tactics inspired by refinery.
module Tactic
  ( Tactic
  , TacticFailure(..)
  , assume
  , introCtr
  , introTuple
  , elim
  , fold
  ) where

import Data.Map qualified as Map
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty

import Control.Effect.Throw
import Control.Effect.Reader
import Control.Effect.Fresh.Named

import Base
import Language.Type
import Language.Expr
import Language.Problem
import Language.Container.Morphism

data TacticFailure
  = NotApplicable
  | TraceIncomplete
  deriving stock (Eq, Ord, Show)

type Tactic sig m =
  ( Has (Reader Context) sig m
  , Has (Reader Problem) sig m
  , Has Fresh sig m
  , Has (Throw Conflict) sig m
  , Has (Throw TacticFailure) sig m
  )

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

caseSplit :: Tactic sig m => Arg -> Problem -> m (Map Name (Arg, Problem))
caseSplit (Arg (Data d ts) terms) prob = do
  cs <- asks $ getConstructors d ts
  let
    e = Map.fromList $ cs <&> \c ->
      ( c.name
      , ( Arg c.value []
        , Problem prob.signature []
        )
      )
    f m (Ctr c x, ex) = Map.adjust (bimap
      (\(Arg ty ys) -> Arg ty (x:ys))
      (\(Problem sig exs) -> Problem sig (ex:exs))) c m
    f _ _ = error "Not a constructor"
  return $ List.foldl' f e (zip terms prob.examples)
caseSplit _ _ = throwError NotApplicable

elim :: Tactic sig m => Name -> m (Program (Named Problem))
elim name = do
  arg <- getArg name
  local (hide name) do
    problem <- ask
    m <- caseSplit arg problem
    arms <- forM (Map.elems m) \(a, p) -> do
      xs <- forM (projections a) (nominate "x")
      hole "_" (addInputs xs p)
    return $ apps (Var "elim") (arms ++ [Var name])

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

    rules <- check restructured

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
        return $ apps (Var "fold") [apps f vars, apps e vars, Var name]

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
        return $ apps (Var "fold") [apps f vars, apps e vars, Var name]

      _ -> throwError NotApplicable -- not implemented for all types
