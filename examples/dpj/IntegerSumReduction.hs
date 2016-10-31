-- IntegerSumReduction
module Main (main) where

import           Data.Foldable (forM_)
import           Data.IORef
import           Data.Monoid (Sum(..))
import           Data.Semigroup (Semigroup(..))
import qualified Data.Vector as V
import           Data.Vector (Vector)
import qualified Data.Vector.Mutable as VM

import           System.IO.Unsafe

type DPJArrayInt     = Vector (Sum Int)
type DPJPartitionInt = Vector DPJArrayInt

sumRef :: IORef (Sum Int)
sumRef = unsafePerformIO $ newIORef 0
{-# NOINLINE sumRef #-}

reduce :: DPJArrayInt -> Int -> IO (Sum Int)
reduce arr tileSize = do
    let segs :: DPJPartitionInt
        segs = stridedPartition arr tileSize

    forM_ segs $ \seg -> forM_ seg updateSum
    readIORef sumRef

-- Not efficient, but eh
stridedPartition :: DPJArrayInt -> Int -> DPJPartitionInt
stridedPartition v n =
  let stride n' = takeWhile (not . null) . map (take n') . iterate (drop n')
  in   V.map V.fromList
     . V.fromList
     . map (map Sum)
     . stride n
     . V.toList
     . V.map getSum
     $ v

-- This should use verified semigroup!
updateSum :: Sum Int -> IO ()
updateSum partialSum = atomicModifyIORef' sumRef $ \x ->
    (x `mappend` partialSum, ())

main :: IO ()
main = do
    let sIZE, tILESIZE :: Int
        sIZE     = 1000000
        tILESIZE = 1000

    arr <- VM.replicate sIZE 0
    VM.write arr 42 42
    arr' <- V.freeze arr
    sum <- reduce arr' tILESIZE
    putStrLn $ "sum=" ++ show sum
