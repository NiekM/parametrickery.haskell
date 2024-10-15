module Language.Relevance where

import Data.Maybe
import Data.Set qualified as Set
import Data.List.NonEmpty qualified as NonEmpty

import Control.Carrier.Error.Either

import Base
import Language.Type
import Language.Container.Morphism
import Language.Problem
import Language.Coverage

subs :: Set a -> [Set a]
subs = Set.toList . Set.powerSet

minimal :: Ord a => [Set a] -> [Set a]
minimal xs = filter (\x -> not $ any (`Set.isProperSubsetOf` x) xs) xs

sufficient :: forall sig m. Has (Reader Context) sig m =>
  Set Name -> Problem -> m (Either Conflict (Signature, [Rule], Coverage))
sufficient xs problem = runError do
  let restricted = onArgs (disable xs) problem
  rules <- check restricted
  cover <- coverage restricted.signature rules
  return (restricted.signature, rules, cover)

newtype Relevance = Relevance
  { relevance :: NonEmpty (Signature, [Rule], Coverage)
  } deriving stock (Eq, Ord, Show)

relevance :: Has (Reader Context) sig m =>
  Problem -> m Relevance
relevance problem = do
  let sets = subs . Set.fromList $ variables problem
  xs <- catMaybes <$> forM sets \set -> do
    s <- sufficient set problem
    return $ (set,) <$> either (const Nothing) return s
  let ss = minimal (map fst xs)
  let ys = map snd . filter ((`elem` ss) . fst) $ xs
  return . Relevance . NonEmpty.fromList $ ys
