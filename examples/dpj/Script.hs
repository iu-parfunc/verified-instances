module Main (main) where

import Data.Foldable (forM_)
import System.Process (callProcess)

runIt :: String -> IO ()
runIt filename = do
  let ghcArgs = [ "-i../../src"
                , filename ++ ".hs"
                , "-O2"
                , "-fforce-recomp"
                , "-threaded"
                , "-rtsopts"
                ]
  callProcess "ghc" ghcArgs
  forM_ [1..16] $ \i -> do
    let exeArgs = [ "+RTS"
                  , "-N" ++ show i
                  , "-T"
                  , "-RTS"
                  , "--regress=allocated:iters"
                  , "--regress=bytesCopied:iters"
                  , "--regress=cycles:iters"
                  , "--regress=numGcs:iters"
                  , "--regress=mutatorWallSeconds:iters"
                  , "--regress=gcWallSeconds:iters"
                  , "--regress=cpuTime:iters"
                  ]
    callProcess ("./" ++ filename) exeArgs

main :: IO ()
main = do
  -- runIt "IntegerSumReduction"
  runIt "IntegerSumReductionNoVerification"
