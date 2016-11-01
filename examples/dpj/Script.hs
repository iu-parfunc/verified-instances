module Main (main) where

import Data.Foldable (forM_)
import System.FilePath ((<.>))
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
    let dumpPrefix = filename ++ "-" ++ show i
        exeArgs = [ "+RTS"
                  , "-N" ++ show i
                  , "-T"
                  , "-RTS"
                  , "--json=" ++ dumpPrefix <.> "json"
                  , "--regress=allocated:iters"
                  , "--regress=bytesCopied:iters"
                  , "--regress=cycles:iters"
                  , "--regress=numGcs:iters"
                  , "--regress=mutatorWallSeconds:iters"
                  , "--regress=gcWallSeconds:iters"
                  , "--regress=cpuTime:iters"
                  ]
    callProcess ("./" ++ filename) exeArgs
    let hfucArgs = [ "--noupload"
                   , "--csv=" ++ dumpPrefix <.> "csv"
                   , "--json"
                   , dumpPrefix <.> "json"
                   ]
    callProcess "hsbencher-fusion-upload-criterion" hfucArgs

main :: IO ()
main = do
  runIt "IntegerSumReduction"
  runIt "IntegerSumReductionNoVerification"
