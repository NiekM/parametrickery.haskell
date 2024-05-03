module Language.Problem where

import Prettyprinter.Utils
import Base
import Language.Expr
import Language.Type
import Language.Container.Morphism

data Problem = Problem
  { sig :: Signature
  , exs :: [Example]
  } deriving stock (Eq, Ord, Show)

-- TODO: before checking the realizability w.r.t. parametricity, it might be
-- good to check whether the type is inhabited. Especially in the case were
-- there are no examples, we should still be able to check automatically that
-- e.g. `{x : a} -> b` is not realizable.
-- TODO: check that this actually works as expected for multiple type variables.
check :: Problem -> Either Conflict [MorphExample]
check (Problem sig exs) = do
  xs <- mapM (checkExample sig) exs
  combine xs

instance Pretty Problem where
  pretty = prettyProblem "_"

prettyProblem :: Text -> Problem -> Doc ann
prettyProblem fun (Problem sig exs) = statements (header : examples)
  where
    header = sep [pretty fun, ":", pretty sig]
    examples = exs <&> \(Example ins out) -> sep
      (pretty fun : map (prettyExpr 3) ins ++ ["=", pretty out])

-- Lifts the nth argument out of a problem.
liftArg :: Nat -> Problem -> Maybe (Text, Mono, [Expr Void], Problem)
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
pickApart :: Problem -> [(Text, Mono, [Expr Void], Problem)]
pickApart p@(Problem Signature { ctxt } _) =
  zipWith const [0 ..] ctxt & mapMaybe \n -> liftArg n p
