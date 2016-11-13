module Main (main) where

import Control.Monad (when)
import Data.Foldable (forM_)
import System.Directory (doesFileExist, removeFile)
import System.FilePath ((<.>))
import System.Process (callProcess)

caps :: [Int]
caps = [1..18]

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
  forM_ caps $ \i -> do
    let dumpPrefix = filename ++ "-" ++ show i
        dumpJSON   = dumpPrefix <.> "json"
        dumpCSV    = dumpPrefix <.> "csv"
        exeArgs = [ "+RTS"
                  , "-N" ++ show i
                  , "-T"
                  , "-RTS"
                  , "--json=" ++ dumpJSON
                  , "--regress=allocated:iters"
                  , "--regress=bytesCopied:iters"
                  , "--regress=cycles:iters"
                  , "--regress=numGcs:iters"
                  , "--regress=mutatorWallSeconds:iters"
                  , "--regress=gcWallSeconds:iters"
                  , "--regress=cpuTime:iters"
                  ]

    e1 <- doesFileExist dumpJSON
    when e1 $ removeFile dumpJSON

    e2 <- doesFileExist dumpCSV
    when e2 $ removeFile dumpCSV

    callProcess ("./" ++ filename) exeArgs
    let hfucArgs = [ "--noupload"
                   , "--csv=" ++ dumpCSV
                   , "--json"
                   , "--custom=CAPABILITIES," ++ show i
                   , dumpPrefix <.> "json"
                   ]
    callProcess "hsbencher-fusion-upload-criterion" hfucArgs

main :: IO ()
main = do
  runIt "IntegerSumReduction"
  runIt "IntegerSumReductionNoVerification"
