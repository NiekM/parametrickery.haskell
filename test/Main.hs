{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE DerivingStrategies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main (main) where

import Data.Text (Text)
import Data.Text.IO qualified as Text
import Data.Maybe (fromJust)
import Test.QuickCheck
import Test.Hspec
import Test.Hspec.QuickCheck
import Prettyprinter

import Data.Named
import Language.Container.Morphism
import Language.Declaration
import Language.Parser
import Refinements

import System.IO.Unsafe qualified as Unsafe
import System.Directory
import Control.Monad

{-# NOINLINE bench #-}
bench :: [Named Problem]
bench = Unsafe.unsafePerformIO do
  xs <- listDirectory "data/bench/"
  forM (reverse xs) \name -> do
    content <- Text.readFile $ "data/bench/" <> name
    return $ parse content

parse :: Parse a => Text -> a
parse = fromJust . lexParse parser

main :: IO ()
main = do
  forM_ bench \(Named name problem) -> do
    print name
    print . pretty $ isFold problem

data Expect = Yay | Nay Conflict
  deriving stock Show

expect :: Expect -> Named Problem -> IO ()
expect e (Named name p) = do
  print name
  case check p of
    Left result -> case e of
      Yay -> do
        print $ "Expected a succes, but got" <+> pretty result
      Nay conflict -> do
        print $ "Expected:" <+> pretty conflict
        print $ "Got: " <+> pretty result
        if conflict == result
          then putStrLn "Success :)"
          else putStrLn "Failure :("
    Right x -> case e of
      Yay -> do
        putStrLn "Realizable, as expected!"
      Nay conflict -> do
        print $ "Expected: " <+> pretty conflict
        putStrLn "Got: Realizable!"
        print x
  putStrLn ""

isFold :: Problem -> [Either Conflict [PolyProblem]]
isFold p = traverse check <$> xs
  where DisCon xs = introFoldr p

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty = either pretty pretty
