{-# LANGUAGE DeriveGeneric #-}

module Benchmark where

import System.Directory
import System.FilePath as Path
import Data.Aeson as Aeson
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Control.Monad as Monad
import GHC.Generics (Generic)
import qualified GHC.Generics as Generics
import Numeric (showFFloat)

import Lib

emptyMark :: Benchmark
emptyMark = Benchmark [] 0 0 0 0 0 0

plusMark :: Benchmark -> Benchmark -> Benchmark
b `plusMark` c =
  b {
    avg = avg b + avg c,
    bigN = bigN b + bigN c,
    bigK = max (bigK b) (bigK c),
    bigD = max (bigD b) (bigD c),
    bigV = bigV b + bigV c,
    bigI = max (bigI b) (bigI c)
  }

summaryMark :: Map String Benchmark -> Benchmark
summaryMark = foldr plusMark emptyMark 

showMark :: Map String Benchmark -> String
showMark bm =
    unlines $ pre ++ titles : Map.foldrWithKey (\k v ss -> entry k v : ss) post bm
  where
    pre = ["\\begin{tabular}{|l|l|l|l|l|l|l|}", "\\hline"]
    titles = concat $ List.intersperse " & " ["Name", "N", "K", "V", "D", "I", "Time (ms)"] ++ ["\\\\\\hline"]
    entry n b = concat $ List.intersperse " & " [n, show $ bigN b, show $ bigK b, show $ bigV b, show $ bigD b, show $ bigI b, showFFloat (Just 2) (fromIntegral (avg b) / fromIntegral 1000000) ""] ++ ["\\\\\\hline"]
    post = ["\\end{tabular}"]

putMark :: FilePath -> Map String Benchmark -> IO ()
putMark fp bm = 
    writeFile fp (showMark bm)

convertMark :: FilePath -> IO ()
convertMark fp =
  do  mbm <- decodeFileStrict fp
      case mbm of
        Nothing -> return ()
        Just bm -> putMark "test.tex" bm

summariseMarks :: FilePath -> IO ()
summariseMarks dir =
    withCurrentDirectory dir $
      do  curDir <- getCurrentDirectory
          jsons <- filter ("json" `Path.isExtensionOf`) <$> listDirectory curDir
          Just bms <- sequence <$> mapM decodeFileStrict jsons
          -- associate the package names with summaries
          let summaries = 
                Map.fromList $ zipWith (\j bm -> (Path.dropExtension j, summaryMark bm)) jsons bms
          putMark "summary.tex" summaries
          Monad.zipWithM_ (\j bm -> putMark (Path.replaceExtension j ".tex") bm) jsons bms

