{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Arbitrary where

import Base
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Tree.Binary

import Test.QuickCheck hiding (total)
import Language.Type
import Language.Expr
import Language.Generics

(|:) :: [a] -> a -> NonEmpty a
xs |: x = foldr NonEmpty.cons (pure x) xs

-- We assume n > 0
divyUp :: Nat -> Nat -> Gen (NonEmpty Nat)
divyUp total n = do
  cuts <- vectorOf (fromIntegral n - 1) $ choose (0, total)
  let starts = 0 :| List.sort cuts
  let ends = List.sort cuts |: total
  return $ NonEmpty.zipWith (-) ends starts

sizedMono :: [Name] -> Nat -> Gen Mono
sizedMono free size = case size of
  0 -> frequency . map (second pure) $
    [ (1, Top)
    , (2, Base Int)
    ] ++ [ (5, Free v) | v <- free ]
  n -> oneof . map snd $ filter fst
    [ (n >= 2,) $ Data "Tree" <$> do
      sizes <- divyUp (n - 2) 2
      forM (NonEmpty.toList sizes) (sizedMono free)
    , (True,) $ Data "List" . pure <$> sizedMono free (n - 1)
    , (True,) $ Data "Maybe" . pure <$> sizedMono free (n - 1)
    , (n == 1, pure $ Data "Bool" [])
    , (n >= 2,) do
      k <- choose (2, min n 3)
      sizes <- divyUp (n - k) k
      Product <$> forM (NonEmpty.toList sizes) (sizedMono free)
    ]

aMono :: [Name] -> Gen Mono
aMono free = sized \n -> choose (0, fromIntegral n) >>= sizedMono free

-- We assume that all free variables are instantiated as Int
aConstant :: Mono -> Gen Value
aConstant = \case
  Free _ -> error "Unexpected free variable"
  Base Int -> resize 5 $ Lit . MkInt <$> arbitrary
  Product ts -> Tuple <$> forM ts (scale (`div` length ts) . aConstant)
  Data "Bool" [] -> toExpr @Bool <$> arbitrary
  Data "List" [t] -> toExpr @[_] <$> liftArbitrary
    (scale (`div` 2) $ aConstant t)
  Data "Maybe" [t] -> toExpr @(Maybe _) <$> liftArbitrary (aConstant t)
  Data "Tree" [t, u] -> toExpr @(Tree _ _) <$> liftArbitrary2
    (scale (`div` 2) $ aConstant t) (scale (`div` 2) $ aConstant u)
  Data t _ -> error $ "Datatype " <> show t <> " not supported"

instance Arbitrary Value where
  arbitrary = aConstant =<< resize 3 (aMono [])
