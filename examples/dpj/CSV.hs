{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import qualified Data.ByteString.Lazy as BL
import           Data.Csv
import           Data.Foldable (forM_)
import qualified Data.Vector as V

import           System.Environment (getArgs)
import           System.FilePath

data Row = Row
  { capabilities :: {-# UNPACK #-} !Int
  , maxTime      :: {-# UNPACK #-} !Double
  }

instance FromNamedRecord Row where
  parseNamedRecord r = Row <$> (floor <$> (r .: "CAPABILITIES" :: Parser Double))
                           <*> r .: "MEDIANTIME"

filenames :: [String]
filenames = ["IntegerSumReduction", "IntegerSumReductionNoVerification"]

caps :: [Int]
caps = [1..16]

main :: IO ()
main = do
  filename:_ <- getArgs
  forM_ caps $ \i -> do
      !csvData <- BL.readFile $ filename ++ "-" ++ show i <.> "csv"
      case decodeByName csvData of
        Left err -> putStrLn err
        Right (_, v) -> do
          putStrLn "THREADS,TIME"
          V.forM_ v $ \p ->
            putStrLn $ show (capabilities p) ++ "," ++ show (maxTime p)
