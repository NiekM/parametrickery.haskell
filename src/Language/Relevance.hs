module Language.Relevance where

import Data.Set qualified as Set
import Data.List.NonEmpty qualified as NonEmpty

import Base
import Language.Type
import Language.Container.Morphism
import Language.Problem
import Language.Coverage

maximal :: Ord a => [Set a] -> [Set a]
maximal xs = filter (\x -> not $ any (x `Set.isProperSubsetOf`) xs) xs

sufficient :: DataContext -> Set Name -> Problem -> Either Conflict (Signature, [Rule], Coverage)
sufficient dataContext xs problem = do
  let restricted = onArgs (disable xs) problem
  rules <- check dataContext restricted
  let cover = coverage dataContext restricted.signature rules
  return (restricted.signature, rules, cover)

newtype Relevance = Relevance
  { relevance :: NonEmpty (Signature, [Rule], Coverage)
  } deriving stock (Eq, Ord, Show)

relevance :: DataContext -> Problem -> Maybe Relevance
relevance dataContext problem = Relevance <$> NonEmpty.nonEmpty ys
  where
    sets = Set.toList . Set.powerSet . Set.fromList $ variables problem
    xs = rights $ sets <&> \set -> (set,) <$> sufficient dataContext set problem
    ss = maximal (map fst xs)
    ys = map snd . filter ((`elem` ss) . fst) $ xs
