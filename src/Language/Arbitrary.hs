{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Arbitrary where

import Base

import Test.QuickCheck
import Language.Type
-- import Language.Expr

arbitraryType :: Context -> [Name] -> Gen Mono
arbitraryType context free = frequency $
  [ (3,) . elements $ map Free free
  , (3,) . oneof $
    context.datatypes <&> \(Named name DataDef { arguments }) -> do
      Data name <$> forM arguments \_ -> arbitraryType context free
  , (3, pure Top)
  , (2, Product <$> vectorOf 2 (arbitraryType context free))
  , (1, Product <$> vectorOf 3 (arbitraryType context free))
  ] where
    -- datatypes = context