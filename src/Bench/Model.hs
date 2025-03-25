module Bench.Model where

import Base

import Data.Either qualified as Either
import Data.Ord qualified as Ord
import Data.Tree.Binary
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty

allSame :: Eq a => [a] -> Bool
allSame [] = True
allSame (x:xs) = all (== x) xs

append :: [a] -> [a] -> [a]
append = (++)

breadthFirst :: Tree a b -> [a]
breadthFirst = List.concat . levels

cartesian :: forall a. [[a]] -> [[a]]
cartesian xss = foldr f [[]] xss
  where
    f :: [a] -> [[a]] -> [[a]]
    f xs yss = foldr g [] xs
      where
        g :: a -> [[a]] -> [[a]]
        g x zss = foldr (\ys qss -> (x:ys):qss) zss yss

clamp :: Ord a => a -> a -> a -> a
clamp x y = Ord.clamp (x, y)

compress :: Eq a => [a] -> [a]
compress = map NonEmpty.head . NonEmpty.group

concat :: [[a]] -> [a]
concat = List.concat

cons :: a -> [a] -> [a]
cons = (:)

copyFirst :: [a] -> [a]
copyFirst [] = []
copyFirst xs@(x:_) = map (const x) xs

copyLast :: [a] -> [a]
copyLast [] = []
copyLast xs = map (const $ List.last xs) xs

deleteMax :: Ord a => [a] -> [a]
deleteMax [] = []
deleteMax xs = List.filter (/= List.maximum xs) xs

depth :: Tree a b -> Int
depth (Leaf _) = 0
depth (Node l _ r) = 1 + max (size l) (size r)

drop :: Int -> [a] -> [a]
drop = List.drop

dupli :: [a] -> [a]
dupli = concatMap \x -> [x, x]

head :: [a] -> Maybe a
head [] = Nothing
head (x:_) = Just x

index :: Int -> [a] -> Maybe a
index = flip (List.!?)

init :: [a] -> [a]
init [] = []
init xs = List.init xs

inorder :: Tree a b -> [a]
inorder (Leaf _) = []
inorder (Node l x r) = inorder l ++ x : inorder r

insert :: Ord a => a -> [a] -> [a]
insert = List.insert

last :: [a] -> Maybe a
last [] = Nothing
last xs = Just $ List.last xs

length :: [a] -> Int
length = List.length

levels :: Tree a b -> [[a]]
levels (Leaf _) = []
levels (Node l x r) = [x] : zipWith (++) (levels l) (levels r)

maximum :: Ord a => [a] -> Maybe a
maximum [] = Nothing
maximum xs = Just $ List.maximum xs

member :: Eq a => a -> [a] -> Bool
member = List.elem

mostCommon :: Eq a => [a] -> Maybe a
mostCommon = pickMax . foldr add []
  where
    pickMax :: [(a, Int)] -> Maybe a
    pickMax ys = fst <$> List.find ((== n) . snd) ys
      where n = List.maximum $ map snd ys

    add :: Eq a => a -> [(a, Int)] -> [(a, Int)]
    add x [] = [(x, 1)]
    add x ((y, n):ys)
      | x == y = (y, n + 1) : ys
      | otherwise = (y, n) : add x ys

nub :: Eq a => [a] -> [a]
nub = List.nub

null :: [a] -> Bool
null = List.null

ordNub :: Ord a => [a] -> [a]
ordNub = List.nub . List.sort

partitionEithers :: [Either a b] -> ([a], [b])
partitionEithers = Either.partitionEithers

pivot :: Ord a => a -> [a] -> ([a], [a])
pivot x xs = (filter (< x) xs, filter (>= x) xs)

preorder :: Tree a b -> [a]
preorder (Leaf _) = []
preorder (Node l x r) = x : preorder l ++ preorder r

replicate :: Nat -> a -> [a]
replicate = List.replicate . fromIntegral

reverse :: [a] -> [a]
reverse = List.reverse

shiftl :: [a] -> [a]
shiftl [] = []
shiftl (x:xs) = xs ++ [x]

shiftr :: [a] -> [a]
shiftr [] = []
shiftr xs = List.last xs : List.init xs

size :: Tree a b -> Int
size (Leaf _) = 0
size (Node l _ r) = 1 + size l + size r

snoc :: a -> [a] -> [a]
snoc x xs = xs ++ [x]

sort :: Ord a => [a] -> [a]
sort = List.sort

sorted :: Ord a => [a] -> Bool
sorted [] = True
sorted (x:xs) = List.and $ List.zipWith (<=) (x:xs) xs

splitAt :: Int -> [a] -> ([a], [a])
splitAt = List.splitAt

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

tail :: [a] -> [a]
tail [] = []
tail (_:xs) = xs

take :: Int -> [a] -> [a]
take = List.take

unzip :: [(a, b)] -> ([a], [b])
unzip = List.unzip

zip :: [a] -> [b] -> [(a, b)]
zip = List.zip
