{-@ LIQUID "--exactdc" @-}
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
import           Data.VerifiedCommutativeSemigroup
import           Data.VerifiedSemigroup

import           Language.Haskell.Liquid.ProofCombinators

{-@ newtype Sum = Sum { getSum :: Int } @-}
newtype Sum = Sum { getSum :: Int }
  deriving (Eq, Ord, Read, Show)

{-@ axiomatize appendSum @-}
appendSum :: Sum -> Sum -> Sum
appendSum x y = Sum (getSum x + getSum y)
{-# INLINE appendSum #-}

instance Semigroup Sum where
  (<>) = appendSum

instance NFData Sum where
  rnf (Sum x) = rnf x

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

{-@
appendSumCommute :: x:Sum -> y:Sum -> { appendSum x y == appendSum y x }
@-}
appendSumCommute :: Sum -> Sum -> Proof
appendSumCommute x y
  =   appendSum x y
  ==. Sum (getSum x + getSum y)
  ==. Sum (getSum y + getSum x)
  ==. appendSum y x
  *** QED

{-@
vsemigroupSum :: VerifiedSemigroup Sum
@-}
vsemigroupSum :: VerifiedSemigroup Sum
vsemigroupSum = VerifiedSemigroup appendSum appendSumAssoc

{-@
vcommutativeSemigroupSum :: VerifiedCommutativeSemigroup Sum
@-}
vcommutativeSemigroupSum :: VerifiedCommutativeSemigroup Sum
vcommutativeSemigroupSum = VerifiedCommutativeSemigroup appendSumCommute vsemigroupSum

type DPJArrayInt     = Vector Sum
type DPJPartitionInt = Vector DPJArrayInt

reduce :: DPJArrayInt -> Int -> IO Sum
reduce arr tileSize = do
    let segs :: DPJPartitionInt
        segs = stridedPartition arr tileSize

    sumref <- newIORef $ Sum 0
    Parallel.forM_ (V.toList segs) $ \seg ->
        updateRef vcommutativeSemigroupSum sumref $ Sum $ V.sum $ unwrapV seg
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

updateRef :: VerifiedCommutativeSemigroup a -> IORef a -> a -> IO ()
updateRef vcs sumref partialSum = atomicModifyIORef' sumref $ \x ->
    (x <<>> partialSum, ())
  where
    (<<>>) = prod (verifiedSemigroup vcs)

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
