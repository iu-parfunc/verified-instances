-- IntegerSumReduction
module Main (main) where

import           Data.IORef
import           Data.Semigroup (Semigroup(..))
import           Data.Vector

import           Unsafe.IO

newtype Sum = Sum Int
  deriving (Eq, Ord, Read, Show)

-- This should use verified semigroup!
instance Semigroup Sum where
  Sum x <> Sum y = Sum (x + y)

type DPJArrayInt     = Vector Sum
type DPJPartitionInt = Vector DPJArrayInt

sumRef :: IORef Sum
sumRef = unsafePerformIO $ newIORef 0
{-# NOINLINE sumRef #-}

reduce :: DPJArrayInt -> Int -> IO Sum
reduce arr tileSize = do
    let segs :: DPJPartitiionInt
        segs = stridedPartition arr tileSize

    forM_ segs $ \seg -> forM_ seg updateSum
    readIORef sumRef

stridedPartition :: DPJArrayInt -> Int -> DPJPartitionInt
stridedPartition = undefined

-- This should use verified semigroup!
updateSum :: Sum -> IO ()
updateSum partialSum = atomicModifyIORef' sumRef $ \x ->
    (x `mappend` partialSum, ())

main :: IO ()
main = do
    let sIZE, tILESIZE :: Int
        sIZE     = 1000000
        tILESIZE = 1000

        arr :: DPJArrayInt
        arr = new sIZE

    write arr 42 42
    sum <- reduce arr tILESIZE
    putStrLn $ "sum=" ++ show sum
