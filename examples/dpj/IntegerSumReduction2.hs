{-@ LIQUID "--exactdc" @-}
module Main where

import Control.DeepSeq
-- import Control.Monad.Par.IO
import Control.Monad.IO.Class
import Data.IORef
import Data.Semigroup (Semigroup(..))

import Control.LVish
import Control.LVish.Unsafe -- for MonadIO Par instance

import Data.Vector.Unboxed as V hiding ((++)) 
import Data.Time.Clock
import Control.Exception
import Prelude as P
import System.Environment
import System.IO.Unsafe (unsafePerformIO)

import           Data.VerifiedCommutativeSemigroup
import           Data.VerifiedSemigroup

import           GHC.Conc

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

-- Untrusted (exports sumStrided)
--------------------------------

tile :: Int
tile = 100000

-- Example 1: a lame, tiled parallel fold:
-- NO racing updates on an accumulator.

{-
sumStrided :: Vector Int -> ParIO Int
sumStrided v = go v []
  where
   go v ls | V.length v <= tile =
             do acc <- P.sum <$> P.mapM get ls
                return $! acc + V.sum v
           | otherwise =
             do let (a,b) = V.splitAt tile v
                xf <- spawn_ $ return $! V.sum a
                go b (xf:ls)
-}

----------------------------------------------------
-- Version 2: divide and conquer tiles, but purely functional
----------------------------------------------------

-- parForTiled :: Maybe HandlerPool -> Int -> (Int, Int) -> (Int -> Par d s ()) -> Par d s ()

-- LVish parallel for loop version:
{-
sumStrided2 :: Vector Int -> Par Int
sumStrided2 v =
  -- Parallel for loop over tile_1 .. tile_n
  let (numTiles,0) = V.length v `quotRem` tile
  -- Hypothetical, parForTree is just for effect:
  ls <- parForTree Nothing (0,numTiles) $ \ tid -> do 
     let myslice = V.slice v (tid * tile) tile 
     return (V.sum myslice)
  sum ls
-}

----------------------------------------------------
-- Version 3: imperative update to accumulator
----------------------------------------------------

sumStrided3 :: Vector Int -> Int
sumStrided3 v =
   unsafePerformIO $ 
   do ref <- runParIO par
      fmap getSum $ readIORef ref
 where
  par :: Par d s (IORef Sum)
  par = do
    -- Paralel for loop over tile_1 .. tile_n
    let (numTiles,0) = V.length v `quotRem` tile
    acc <- newRV $ Sum 0
    -- hp <- newHandlerPool
    -- Note this is asynchronous and will return immediately:    
    parForTree (0,numTiles) $ \ tid -> do 
      let myslice = V.slice (tid * tile) tile v
      updateRV vcommutativeSemigroupSum acc (Sum $ V.sum myslice)

    -- quasideterminism:
    -- quiesce hp
    -- freeze acc    
    -- We can return the var itself from the computation:
    return $ getRV acc

------------------------------------------------------
-- Trusted below here
------------------------------------------------------

-- LVar instance would provide Frz type family:
-- Frz(ReductionVar s Int) -> ReductionVar Frzn Int
  
newtype ReductionVar s a = RV { getRV :: IORef a }

-- IMAGINE that these are type class constraints:
updateRV :: VerifiedCommutativeSemigroup a -> ReductionVar s a -> a -> Par d s ()
updateRV vcs (RV ref) partialSum = liftIO $ atomicModifyIORef' ref $ \x ->
      (x <<>> partialSum, ())
  where
    (<<>>) = prod (verifiedSemigroup vcs)

newRV :: a -> Par d s (ReductionVar s a)
newRV = liftIO . fmap RV . newIORef

main :: IO ()
main = do
  vecsize:_ <- getArgs
  doIt (read vecsize)

doIt :: Int -> IO ()
doIt vecsize = do
  let v = V.replicate vecsize 99
  _ <- evaluate v
  st <- getCurrentTime
  sm <- evaluate $ sumStrided3 v
  en <- getCurrentTime
  putStrLn $ "Sum: "  ++ show sm
  putStrLn $ "Time: " ++ show (diffUTCTime en st)
  
{-  
main :: IO ()
main = do
  c <- getNumCapabilities
  defaultMain
    [env setup $ \arr -> bench ("reduce (" ++ show c ++ " threads)")
                           $ nfIO $ reduce arr tILESIZE]
-}
