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

stridedPartition :: DPJArrayInt -> Int -> DPJPartitionInt
stridedPartition = undefined

-- This should use verified semigroup!
updateSum :: Sum Int -> IO ()
updateSum partialSum = atomicModifyIORef' sumRef $ \x ->
    (x `mappend` partialSum, ())

main :: IO ()
main = do
    let sIZE, tILESIZE :: Int
        sIZE     = 1000000
        tILESIZE = 1000

    arr <- VM.new sIZE
    VM.write arr 42 42
    arr' <- V.freeze arr
    sum <- reduce arr' tILESIZE
    putStrLn $ "sum=" ++ show sum
