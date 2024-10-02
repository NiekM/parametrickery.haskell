module Language.Relevance where

import Data.Maybe
import Data.Set qualified as Set
import Data.List.NonEmpty qualified as NonEmpty

import Base
import Data.Named
import Language.Type
import Language.Container.Morphism
import Language.Problem
import Language.Coverage

subs :: Set a -> [Set a]
subs = Set.toList . Set.powerSet

minimal :: Ord a => [Set a] -> [Set a]
minimal xs = filter (\x -> not $ any (`Set.isProperSubsetOf` x) xs) xs

getError :: Has (Error e) sig m => m a -> m (Either e a)
getError m = catchError (Right <$> m) (return . Left)

sufficient :: (Has (Reader Context) sig m, Has (Error Conflict) sig m)
  => Set Text -> Problem -> m (Either Conflict (Signature, [Rule], Coverage))
sufficient xs problem = getError do
  let restricted = onArgs (restrict xs) problem
  rules <- check restricted
  cover <- coverage restricted.signature rules
  return (restricted.signature, rules, cover)

newtype Relevance = Relevance
  { relevance :: NonEmpty (Signature, [Rule], Coverage)
  } deriving stock (Eq, Ord, Show)

relevance :: (Has (Reader Context) sig m, Has (Error Conflict) sig m)
  => Problem -> m Relevance
relevance problem = do
  let vars = problem.signature.context <&> (.name)
  let sets = subs $ Set.fromList vars
  xs <- catMaybes <$> forM sets \set -> do
    s <- sufficient set problem
    return $ (set,) <$> either (const Nothing) return s
  let ss = minimal (map fst xs)
  let ys = map snd . filter ((`elem` ss) . fst) $ xs
  return . Relevance . NonEmpty.fromList $ ys
