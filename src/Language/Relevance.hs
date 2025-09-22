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

maximal :: Ord a => [Set a] -> [Set a]
maximal xs = filter (\x -> not $ any (x `Set.isProperSubsetOf`) xs) xs

sufficient :: DataContext -> Set Name -> Problem -> Either Conflict (Signature, [Rule], Coverage)
sufficient dataContext xs problem = do
  let restricted = onArgs (disable xs) problem
  rules <- check dataContext restricted
  let cover = coverage dataContext restricted.signature rules
  return (restricted.signature, rules, cover)

-- newtype Relevance = Relevance
--   { relevance :: NonEmpty (Signature, [Rule], Coverage)
--   } deriving stock (Eq, Ord, Show)
--
-- relevance :: DataContext -> Problem -> Relevance
-- relevance dataContext problem = do
--   let sets = subs . Set.fromList $ variables problem
--   xs <- catMaybes <$> forM sets \set -> do
--     s <- sufficient dataContext set problem
--     return $ (set,) <$> either (const Nothing) return s
--   let ss = maximal (map fst xs)
--   let ys = map snd . filter ((`elem` ss) . fst) $ xs
--   return . Relevance . NonEmpty.fromList $ ys
