module Main (main) where

import Control.Exception
import Data.Foldable
import Data.Function
import Data.List
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.Process

main :: IO ()
main = do
  mbCabalHead <- lookupEnv "CABAL_HEAD"
  let cabalHead = case mbCabalHead of
                    Just path -> path
                    Nothing   -> "cabal"
  hsFiles' <- map ("src" </>) .
              filter ((== ".hs") . takeExtension) <$> getDirectoryContentsRecursive "src"
  let hsFiles = hsFiles' \\ [ "src/GenericProofs/TH.hs" -- Infinitely loops for some reason
                            ]
                         & filter (not . isPrefixOf "src/GenericProofs/VerifiedFunctor")
  putStrLn "Preparing to run liquid on:"
  forM_ hsFiles $ \hsFile -> putStrLn $ '\t':hsFile
  forM_ hsFiles $ \hsFile -> do
    let cmd = cabalHead ++ " new-run liquid -- -iinclude -isrc " ++ hsFile
    putStrLn cmd
    (_, _, _, handle) <- createProcess $ shell cmd
    ex <- waitForProcess handle
    case ex of
      ExitSuccess   -> return ()
      ExitFailure{} -> throw ex

getDirectoryContentsRecursive :: FilePath -> IO [FilePath]
getDirectoryContentsRecursive dir0 =
  fmap tail (recurseDirectories dir0 [""])

recurseDirectories :: FilePath -> [FilePath] -> IO [FilePath]
recurseDirectories _    []         = return []
recurseDirectories base (dir:dirs) = do
  (files, dirs') <- collect [] [] =<< getDirectoryContents (base </> dir)

  files' <- recurseDirectories base (dirs' ++ dirs)
  return (dir : files ++ files')

  where
    collect files dirs' []              = return (reverse files, reverse dirs')
    collect files dirs' (entry:entries) | ignore entry
                                        = collect files dirs' entries
    collect files dirs' (entry:entries) = do
      let dirEntry  = dir </> entry
          dirEntry' = addTrailingPathSeparator dirEntry
      isDirectory <- doesDirectoryExist (base </> dirEntry)
      if isDirectory
        then collect files (dirEntry':dirs') entries
        else collect (dirEntry:files) dirs' entries

    ignore ['.']      = True
    ignore ['.', '.'] = True
    ignore _ = False
