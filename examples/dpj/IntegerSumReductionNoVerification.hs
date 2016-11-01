module Main (main) where

import           Control.DeepSeq (NFData(..))
import qualified Control.Monad.Parallel as Parallel

import           Criterion.Main

import           Data.Coerce
import qualified Data.Foldable as Sequential (forM_)
import           Data.IORef
import           Data.Semigroup (Semigroup(..))
import qualified Data.Vector as V
import           Data.Vector (Vector)
import qualified Data.Vector.Mutable as VM

newtype Sum = Sum { getSum :: Int }
  deriving (Eq, Ord, Read, Show)

appendSum :: Sum -> Sum -> Sum
appendSum x y = Sum (getSum x + getSum y)
{-# INLINE appendSum #-}

instance Semigroup Sum where
  (<>) = appendSum

instance NFData Sum where
  rnf (Sum x) = rnf x

type DPJArrayInt     = Vector Sum
type DPJPartitionInt = Vector DPJArrayInt

reduce :: DPJArrayInt -> Int -> IO Sum
reduce arr tileSize = do
    let segs :: DPJPartitionInt
        segs = stridedPartition arr tileSize

    sumref <- newIORef $ Sum 0
    Parallel.forM_ (V.toList segs) $ \seg ->
        updateRef sumref $ Sum $ V.sum $ unwrapV seg
    readIORef sumref
  where
    unwrapV :: Vector Sum -> Vector Int
    unwrapV = coerce

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

updateRef :: Semigroup a => IORef a -> a -> IO ()
updateRef sumref partialSum = atomicModifyIORef' sumref $ \x ->
    (x <> partialSum, ())

main :: IO ()
main = defaultMain
  [ env setup $ \arr -> bench "reduce" $ nfIO $ reduce arr tILESIZE
  ]

sIZE, tILESIZE :: Int
sIZE     = 1000000
tILESIZE = 1000

setup :: IO DPJArrayInt
setup = do
    arr <- VM.replicate sIZE $ Sum 0
    VM.write arr 42 $ Sum 42
    V.freeze arr
