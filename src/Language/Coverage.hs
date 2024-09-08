module Language.Coverage (Coverage(..), coverage) where

import Control.Monad.State
import Data.List qualified as List
import Data.Set qualified as Set
import Data.Map.Strict qualified as Map

import Base
import Data.Named
import Language.Expr
import Language.Type
import Language.Container
import Language.Container.Morphism
import Language.Container.Relation
import Language.Declaration

-- TODO: how do we calculate the positions? afterwards?
coveringShapes :: Mono -> Maybe [Expr Text]
coveringShapes = \case
  Free a -> return [Hole $ MkHole a]
  Product ts -> do
    xss <- traverse coveringShapes ts
    return $ Tuple <$> sequence xss
  Sum ts -> do
    xss <- traverse coveringShapes ts
    let n = List.genericLength ts
    return . concat $ zipWith (\i xs -> Proj i n <$> xs) [0..] xss
  List t -> do
    -- We can only cover all possible lists if it is a list of voids.
    [] <- coveringShapes t
    return [Lst []]
  Base Int -> Nothing
  Base Bool -> return $ map (Lit . MkBool) [False, True]

anywhere :: (a -> b -> [b]) -> (a -> b) -> a -> [b] -> [[b]]
anywhere _ e x [] = [[e x]]
anywhere f e x (y:ys) = (f x y ++ ys) : map (y:) (anywhere f e x ys)

prependAnywhere :: a -> [[a]] -> [[[a]]]
prependAnywhere = anywhere (\x xs -> [x:xs]) return

-- | All possible ways to divide a list into non-empty sublists.
subs :: [a] -> [[[a]]]
subs = List.foldr (concatMap . prependAnywhere) [[]]

insertAnywhere :: a -> [a] -> [[a]]
insertAnywhere = anywhere (\x y -> [x, y]) id

orderings :: [a] -> [[a]]
orderings = List.foldr (concatMap . insertAnywhere) [[]]

coveringRelations :: [Position] -> Constraint -> [Relation]
coveringRelations ps = \case
  Eq a ->
    let qs = filter (\x -> x.var == a) ps
    in RelEq . Set.fromList . map Set.fromList <$> subs qs
  Ord a ->
    let qs = filter (\x -> x.var == a) ps
    in RelOrd . map Set.fromList <$> concatMap orderings (subs qs)

unTuple :: Expr h -> [Expr h]
unTuple (Tuple xs) = xs
unTuple _ = error "Expected Tuple"

toShape :: Expr Text -> Shape
toShape expr = flip evalState mempty $ forM expr \v -> do
  m <- get
  let n = fromMaybe 0 $ Map.lookup v m
  modify $ Map.insert v (n + 1)
  return $ Position v n

-- Computes all shapes and relations required for coverage (if possible)
coveringPatterns :: [Constraint] -> [Mono] -> Maybe [Pattern]
coveringPatterns constraints context = do
  shapes <- map toShape <$> coveringShapes (Product context)
  concat <$> forM shapes \shape -> do
    let
      inputs = unTuple shape
      positions = holes shape
      relations = traverse (coveringRelations positions) constraints
    return $ Pattern inputs <$> relations

signatureCoverage :: Signature -> Maybe (Set Pattern)
signatureCoverage signature = Set.fromList <$> coveringPatterns
  signature.constraints
  (map (.value) signature.context)

bindingCoverage :: [PolyExample] -> Set Pattern
bindingCoverage = Set.fromList <$> fmap (.input)

data Coverage = Total | Partial | Missing (Set Pattern)
  deriving (Eq, Ord, Show)

instance Pretty Coverage where
  pretty = \case
    Total -> "Total"
    Partial -> "Partial"
    Missing c -> vcat $ "Partial, missing cases:"
      : map pretty (Set.toList c)

-- TODO: how do we do this? Perhaps we can have some "coverable" property of
-- type? Where we generate all required input shapes and relations to have
-- coverage or Nothing if coverage is not possible (like for lists). This would
-- make it easy to report missing coverage.
coverage :: PolyProblem -> Coverage
coverage problem = case signatureCoverage problem.signature of
  Nothing -> Partial
  Just possible ->
    let
      covered = bindingCoverage problem.bindings
      missing = possible Set.\\ covered
    in if null missing then Total else Missing missing