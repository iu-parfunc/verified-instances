{-@ LIQUID "--exactdc" @-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Main (main) where

import           Data.Foldable (forM_)
import           Data.IORef
import           Data.Semigroup (Semigroup(..))
import qualified Data.Vector as V
import           Data.Vector (Vector)
import qualified Data.Vector.Mutable as VM

import           Language.Haskell.Liquid.ProofCombinators

import           System.IO.Unsafe

{-@ newtype Sum = Sum { getSum :: Int } @-}
newtype Sum = Sum { getSum :: Int }
  deriving (Eq, Ord, Read, Show)

{-@ axiomatize appendSum @-}
appendSum :: Sum -> Sum -> Sum
appendSum x y = Sum (getSum x + getSum y)
{-# INLINE appendSum #-}

instance Semigroup Sum where
  (<>) = appendSum

{-@
getSumSumId :: x:Int -> { getSum (Sum x) == x }
@-}
getSumSumId :: Int -> Proof
getSumSumId x = getSum (Sum x) ==. x *** QED

{-@
appendSumAssoc :: x:Sum -> y:Sum -> z:Sum
               -> { appendSum x (appendSum y z) == appendSum (appendSum x y) z }
@-}
appendSumAssoc :: Sum -> Sum -> Sum -> Proof
appendSumAssoc x y z
  =   appendSum x (appendSum y z)
  ==. appendSum x (Sum (getSum y + getSum z))
  ==. Sum (getSum x + getSum (Sum (getSum y + getSum z)))
  ==. Sum (getSum x + (getSum y + getSum z)) ? getSumSumId (getSum (Sum (getSum y + getSum z)))
  ==. Sum ((getSum x + getSum y) + getSum z)
  ==. Sum (getSum (Sum (getSum x + getSum y)) + getSum z) ? getSumSumId (getSum (Sum (getSum x + getSum y)))
  ==. appendSum (Sum (getSum x + getSum y)) z
  ==. appendSum (appendSum x y) z
  *** QED

{-
{-@@-}
appendSumCommute :: x:Sum -> y:Sum -> { appendSum x y == appendSum y x }
appendSumCommute :: Sum -> Sym -> Proof
-}

type DPJArrayInt     = Vector Sum
type DPJPartitionInt = Vector DPJArrayInt

sumRef :: IORef Sum
sumRef = unsafePerformIO $ newIORef $ Sum 0
{-# NOINLINE sumRef #-}

reduce :: DPJArrayInt -> Int -> IO Sum
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
updateSum :: Sum -> IO ()
updateSum partialSum = atomicModifyIORef' sumRef $ \x ->
    (x <> partialSum, ())

main :: IO ()
main = do
    let sIZE, tILESIZE :: Int
        sIZE     = 1000000
        tILESIZE = 1000

    arr <- VM.replicate sIZE $ Sum 0
    VM.write arr 42 $ Sum 42
    arr' <- V.freeze arr
    theSum <- reduce arr' tILESIZE
    putStrLn $ "sum=" ++ show theSum
