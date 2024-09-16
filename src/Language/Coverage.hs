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

coveringShapes :: [Datatype] -> Mono -> Maybe [Expr Text]
coveringShapes defs = go []
  where
    -- We keep track of datatype names to recognize recursion.
    go :: [Text] -> Mono -> Maybe [Expr Text]
    go recs = \case
      -- Holes remember their type, so that we can fill in the positions later.
      Free a -> return [Hole $ MkHole a]
      Product ts -> do
        xss <- traverse (go recs) ts
        return $ Tuple <$> sequence xss
      Data d ts
        | d `elem` recs -> Nothing
        | otherwise ->
          concat <$> forM (getConstructors d ts defs) \(Constructor c t) -> do
            xs <- go (d : recs) t
            return $ Ctr c <$> xs
      Base Int -> Nothing

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
coveringPatterns :: [Datatype] -> [Constraint] -> [Mono] -> Maybe [Pattern]
coveringPatterns defs constraints context = do
  shapes <- map toShape <$> coveringShapes defs (Product context)
  concat <$> forM shapes \shape -> do
    let
      inputs = unTuple shape
      positions = holes shape
      relations = traverse (coveringRelations positions) constraints
    return $ Pattern inputs <$> relations

expectedCoverage :: [Datatype] -> Signature -> Maybe (Set Pattern)
expectedCoverage defs signature = Set.fromList <$> coveringPatterns defs
  signature.constraints
  (map (.value) signature.context)

bindingCoverage :: [PolyExample] -> Set Pattern
bindingCoverage = Set.fromList <$> map (.input)

data Coverage = Total | Partial | Missing (Set Pattern)
  deriving (Eq, Ord, Show)

instance Pretty Coverage where
  pretty = \case
    Total -> "Total"
    Partial -> "Partial"
    Missing c -> vcat $ "Partial, missing cases:"
      : map pretty (Set.toList c)

-- TODO: what kind of coverage do we need? how do we check shape coverage
-- nicely? maybe translate to Map Shape Relation? might be better in general as
-- coverage result. even if shapes are missing, we still want to know which
-- relations are missing for other shapes. if a shape is missing, do we also
-- still want to return which relations go with that shape? if there are too
-- many shapes to cover, because of e.g. a list as input, do we still want to
-- have relation coverage? or subpattern coverage, e.g. if it's a list booleans,
-- do we still want coverage checking for a pattern such as [True], letting us
-- know that we are missing [False]?
coverage :: [Datatype] -> PolyProblem -> Coverage
coverage defs problem = case expectedCoverage defs problem.signature of
  Nothing -> Partial
  Just expected ->
    let
      covered = bindingCoverage problem.bindings
      missing = expected Set.\\ covered
      -- shapes = Set.map (.shapes) expected Set.\\ Set.map (.shapes) covered
    in if null missing then Total else Missing missing
