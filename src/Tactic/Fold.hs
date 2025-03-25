{-# OPTIONS_GHC -Wno-ambiguous-fields #-}
module Tactic.Fold where

import Base
import Control.Effect.Fresh.Named
import Control.Carrier.Error.Either
import Data.List qualified as List

import Language.Expr
import Language.Problem
import Language.Type
import Language.Container
import Language.Container.Morphism

import Tactic

fold :: Tactic sig m => Name -> m Filling
fold name = cata name `andThen` do
  elim =<< asks (List.last . variables)

liftThrow :: Has (Throw e) sig m => (d -> e) -> ErrorC d m a -> m a
liftThrow f m = runError m >>= \case
  Left e -> throwError $ f e
  Right x -> return x

getBaseFunctor :: Tactic sig m => Mono -> m (Name, [Mono])
getBaseFunctor = \case
  Data d ts -> do
    let baseFunctor = d <> "F"
    ds <- ask @Context
    case find baseFunctor ds.datatypes of
      Nothing -> throwError $ NotApplicable "cannot unroll nonrecursive datatype"
      _ -> return ()
    return (baseFunctor, ts)
  _ -> throwError $ NotApplicable "cannot unroll nondatatype"

unroll :: Tactic sig m => Mono -> Term Void -> m (Term (Term Void))
unroll mono term = do
  (baseFunctor, types) <- getBaseFunctor mono
  matched <- poly (Data baseFunctor (types ++ [Free "r"])) term
  return $ matched >>= \case
    ("r", x) -> return x
    (_, other) -> absurd <$> other

cata :: Tactic sig m => Name -> m Filling
cata name = do
  Arg mono terms <- getArg name
  local (hide [name]) do
    problem <- ask @Problem

    rules <- liftThrow Unrealizable $ check Problem
      { signature = problem.signature
        { inputs = Named name mono : problem.signature.inputs }
      , examples = zip terms problem.examples <&>
        \(i, Example is o) -> Example (i:is) o
      }

    let recurse = applyRules rules

    unrolled <- forM terms $ unroll mono

    examples <- forM (zip unrolled problem.examples)
      \(argument, Example inputs output) -> do
        fixed <- join <$> forM argument \x ->
          maybe (throwError TraceIncomplete) pure $ recurse (x:inputs)
        return $ Example (inputs ++ [fixed]) output

    (baseFunctor, types) <- getBaseFunctor mono

    r <- freshName "r"
    f <- local (const $ Problem problem.signature
      { inputs = problem.signature.inputs ++
        [ Named r $ Data baseFunctor (types ++ [problem.signature.output]) ]
      } examples) $ hole True

    let result = Apps (Var "cata") [Lams [r] f, Var name]
    return result

para :: Tactic sig m => Name -> m Filling
para name = do
  Arg mono terms <- getArg name
  local (hide [name]) do
    problem <- ask @Problem

    rules <- liftThrow Unrealizable $ check Problem
      { signature = problem.signature
        { inputs = Named name mono : problem.signature.inputs }
      , examples = zip terms problem.examples <&>
        \(i, Example is o) -> Example (i:is) o
      }

    let recurse = applyRules rules

    unrolled <- forM terms $ unroll mono

    examples <- forM (zip unrolled problem.examples)
      \(argument, Example inputs output) -> do
        fixed <- join <$> forM argument \x ->
          maybe (throwError TraceIncomplete) (pure . Tuple . (:[x])) $ recurse (x:inputs)
        return $ Example (inputs ++ [fixed]) output

    (baseFunctor, types) <- getBaseFunctor mono

    r <- freshName "r"
    f <- local (const $ Problem problem.signature
      { inputs = problem.signature.inputs ++
        [ Named r $ Data baseFunctor (types ++
          [Product [problem.signature.output, mono]])
        ]
      } examples) $ hole True

    let result = Apps (Var "para") [Lams [r] f, Var name]

    return result

