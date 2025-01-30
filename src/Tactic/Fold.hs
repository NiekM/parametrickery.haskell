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
          Nothing -> throwError $ NotApplicable "not a recursive datatype"
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
          } examples) $ hole True

        let result = Apps (Var "cata") [Lams [r] f, Var name]
        return result

      _ -> throwError $ NotApplicable "not a datatype"

