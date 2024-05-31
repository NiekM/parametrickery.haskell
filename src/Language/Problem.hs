module Language.Problem where

import Data.Map.Strict qualified as Map

import Prettyprinter.Utils
import Base
import Data.Map.Multi qualified as Multi
import Language.Expr
import Language.Type
import Language.Container.Relation
import Language.Container.Morphism

data Problem = Problem
  { signature :: Signature
  , examples  :: [Example]
  } deriving stock (Eq, Ord, Show)

-- TODO: before checking the realizability w.r.t. parametricity, it might be
-- good to check whether the type is inhabited. Especially in the case were
-- there are no examples, we should still be able to check automatically that
-- e.g. `{x : a} -> b` is not realizable.
-- TODO: check that this actually works as expected for multiple type variables.
check :: Problem -> Either Conflict PolyProblem
check (Problem signature exs) = do
  xs <- mapM (checkExample signature) exs
  examples <- combine xs
  return PolyProblem { signature, examples }

instance Pretty Problem where
  pretty = prettyProblem "_"

prettyProblem :: Text -> Problem -> Doc ann
prettyProblem fun (Problem sig exs) = statements (header : examples)
  where
    header = sep [pretty fun, ":", pretty sig]
    examples = exs <&> \(Example ins out) -> sep
      (pretty fun : map (prettyExpr 3) ins ++ ["=", pretty out])

-- Lifts the nth argument out of a problem.
liftArg :: Nat -> Problem -> Maybe (Text, Mono, [Term], Problem)
liftArg n (Problem sig@Signature { ctxt } exs)
  | n >= fromIntegral (length ctxt) = Nothing
  | otherwise = Just (name, mono, exprs, Problem sig { ctxt = ctxt' } exs')
  where
    ((name, mono), ctxt') = pick n ctxt
    (exprs, exs') = unzip $ pickEx <$> exs

    pickEx (Example (pick n -> (i, ins)) out) = (i, Example ins out)

    pick :: Nat -> [a] -> (a, [a])
    pick i xs = case splitAt (fromIntegral i) xs of
      (ys, z:zs) -> (z, ys ++ zs)
      _ -> error "Error"

-- All possible ways to lift one argument from a problem.
pickApart :: Problem -> [(Text, Mono, [Term], Problem)]
pickApart p@(Problem Signature { ctxt } _) =
  zipWith const [0..] ctxt & mapMaybe \n -> liftArg n p

data PolyProblem = PolyProblem
  { signature :: Signature
  , examples  :: [PolyExample]
  } deriving stock (Eq, Ord, Show)

instance Pretty PolyProblem where
  pretty = prettyPolyProblem "_"

prettyPolyProblem :: Text -> PolyProblem -> Doc ann
prettyPolyProblem fun (PolyProblem sig exs) = statements (header : examples)
  where
    header = sep [pretty fun, ":", pretty sig]
    examples = exs <&> \(PolyExample r ss t o) ->
      let
        arguments = sep (pretty fun : map (prettyExpr 3) ss)
        relations = map pretty . filter relevant $ Map.elems r
        output = pretty $ t <&> \p -> PrettySet $ Multi.lookup p o
      in if null relations
        then arguments <+> "=" <+> output
        else arguments <+> encloseSep "| " " =" ", " relations <+> output
