module Language.Problem where

import Prettyprinter.Utils
import Base
import Language.Expr
import Language.Type
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
check :: Problem -> Result PolyProblem
check (Problem signature exs) = do
  xs <- mapM (checkExample signature) exs
  examples <- combine xs
  return PolyProblem { signature, examples }

instance Pretty Problem where
  pretty = prettyNamed "_"

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
  pretty = prettyNamed "_"

instance Pretty (Named PolyProblem) where
  pretty (Named name (PolyProblem sig exs)) = statements (header : examples)
    where
      header   = prettyNamed name sig
      examples = prettyNamed name <$> exs

instance Pretty (Named Problem) where
  pretty (Named name (Problem sig exs)) = statements (header : examples)
    where
      header   = prettyNamed name sig
      examples = prettyNamed name <$> exs
