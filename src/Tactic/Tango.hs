module Tactic.Tango where

import Base
import Control.Effect.Fresh.Named
import Language.Expr
import Language.Type
import Language.Problem
import Tactic.Core
import Tactic.Hole
import Tactic.Ignore

tango :: Tactic sig m => Name -> Name -> m Filling
tango name1 name2 = do
  Arg t _ <- getArg name1
  Arg u _ <- getArg name2
  case (t, u) of
    (Data "List" [a], Data "List" [b]) -> do
      let mono = Data "TangoListList" [a, b]
      let program = Apps (Var "tango") [Var name1, Var name2]
      introLet "xys" program mono >>> ignore name1 >>> ignore name2
    (Data "List" [a], Data "Nat" []) -> do
      let mono = Data "TangoListNat" [a]
      let program = Apps (Var "tango") [Var name1, Var name2]
      introLet "xys" program mono >>> ignore name1 >>> ignore name2
    _ -> throwError $ NotApplicable "Only works for lists"

-- ghci> PROGRAM p = synthesize def { tactic = Tactic.introLet "xys" (Apps (Var "tango") [Var "xs", Var "_ys"]) (Data "TangoListList" [Free "a", Fr

-- introLet :: Tactic sig m => Named Arg -> m Filling
-- introLet arg = do
--   local (onArgs \(Args ins out) -> Args (arg:ins) out) $ hole
--
introLet :: Tactic sig m => Name -> Program Void -> Mono -> m Filling
introLet name expr mono = do
  problem <- ask
  case evaluate expr problem of
    Nothing -> throwError $ NotApplicable "expression fails to evaluate"
    Just values -> do
      x <- freshName name
      let new = Named x (Arg mono values)
      local (onArgs \(Args ins out) -> Args (new:ins) out) do
        h <- hole
        return $ App (Lam x h) (vacuous expr)

exact :: Tactic sig m => Program Void -> Mono -> m Filling
exact expr t = do
  problem <- ask
  out <- asks outputArg
  when (t /= out.mono) $ throwError $ NotApplicable "expression has incorrect typ"
  case evaluate expr problem of
    Nothing -> throwError $ NotApplicable "expression does not evaluate to a Value"
    Just result | result == (outputArg problem).terms -> return $ vacuous expr
    _ -> throwError $ NotApplicable "expression does not match output"

-- map :: Tactic sig m => Name -> m Filling
-- map name = do
--   Arg mono terms <- getArg name
--   local (hide [name]) do
--     problem <- ask @Problem
--     case (mono, problem.signature.output) of
--       (Data "List" [t], Data "List" [u]) -> do
--         examples <- forM (zip terms problem.examples) \case
--           (List inputs, Example scope (List outputs)) -> do
--             unless (length inputs == length outputs) $ throwError $ PropagationError "input and output length don't match"
--             return $ zipWith (\x y -> Example (scope ++ [x]) y) inputs outputs
--           _ -> error "Not actually lists."
--         x <- freshName "x"
--         let Signature constraints context _ = problem.signature
--         let signature = Signature constraints (context ++ [Named x t]) u
--         let subproblem = Problem signature $ concat examples
--         local (const subproblem) do
--           f <- rerealize hole
--           let result = Apps (Var "map") [Lams [x] f, Var name]
--           return result
--       _ -> throwError $ NotApplicable "map only implemented for lists"

