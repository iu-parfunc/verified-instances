{-# LANGUAGE BangPatterns #-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--totality"       @-}
{-@ LIQUID "--exactdc"        @-}
{-@ LIQUID "--prune-unsorted" @-}

module Main where

import Criterion.Main
import GHC.Conc                                 (getNumCapabilities)

import Control.DeepSeq
import Data.IORef
import Data.Semigroup                           (Semigroup (..))

import Control.LVish
import Control.LVish.Internal

import Control.Exception
import Data.Time.Clock
import Data.Vector.Unboxed                      as V hiding ((++), empty)
import Prelude                                  as P
import System.Environment
import System.IO.Unsafe                         (unsafePerformIO)

import VerifiedAbelianMonoid

import GHC.Conc

import Language.Haskell.Liquid.ProofCombinators

{-@ newtype Sum = Sum { getSum :: Int } @-}
newtype Sum = Sum { getSum :: Int }
  deriving (Eq, Ord, Read, Show)

{-@ axiomatize appendSum @-}
appendSum :: Sum -> Sum -> Sum
appendSum x y = Sum (getSum x + getSum y)
{-# INLINE appendSum #-}

{-@ axiomatize emptySum @-}
emptySum :: Sum
emptySum = Sum 0
{-# INLINE emptySum #-}

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
  ==. Sum (getSum x + (getSum y + getSum z))
  ==. Sum ((getSum x + getSum y) + getSum z)
  ==. Sum (getSum (Sum (getSum x + getSum y)) + getSum z)
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
appendIntLident :: x:Int -> { 0 + x == x }
@-}
appendIntLident :: Int -> Proof
appendIntLident x = 0 + x ==. x *** QED

{-@
assume appendSumLident :: x:Sum -> { appendSum emptySum x == x }
@-}
appendSumLident :: Sum -> Proof
appendSumLident x
  =   appendSum emptySum x
  ==. appendSum (Sum 0) x
  ==. Sum (getSum (Sum 0) + getSum x)
  ==. Sum (0 + getSum x) ? getSumSumId 0
  ==. Sum (getSum x) ? appendIntLident (getSum x)
  ==. x
  *** QED

{-@
assume appendSumRident :: x:Sum -> { appendSum x emptySum == x }
@-}
appendSumRident :: Sum -> Proof
appendSumRident x@(Sum s)
  =   appendSum x emptySum
  ==. appendSum x (Sum 0)
  ==. Sum (s + getSum (Sum 0))
  ==. Sum (s + 0)
  ==. Sum s
  ==. x
  *** QED

{-@
vamSum :: VerifiedAbelianMonoid Sum
@-}
vamSum :: VerifiedAbelianMonoid Sum
vamSum = VAM emptySum         appendSum
             appendSumCommute appendSumAssoc
             appendSumLident  appendSumRident

-- Untrusted (exports sumStrided)
--------------------------------

{-@ tile :: {v:Int|v>0} @-}
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
   do ref <- runParPolyIO par
      fmap getSum $ readIORef ref
 where
  par :: Par d s (IORef Sum)
  par = do
    -- Paralel for loop over tile_1 .. tile_n
    let (numTiles, _) = V.length v `quotRem` tile
    acc <- newRV $ Sum 0
    -- hp <- newHandlerPool
    -- Note this is asynchronous and will return immediately:
    parForSimple (0,numTiles) $ \ tid -> do
      let myslice = V.slice (tid * tile) tile v
      let x = (Sum $ V.sum myslice)
      updateRV vamSum acc x

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
updateRV :: VerifiedAbelianMonoid a -> ReductionVar s a -> a -> Par d s ()
updateRV vam (RV ref) !partialSum = liftIO $ atomicModifyIORef' ref $ \x ->
      (x <<>> partialSum, ())
  where
    (<<>>) = append vam

newRV :: a -> Par d s (ReductionVar s a)
newRV = liftIO . fmap RV . newIORef

main :: IO ()
main = do
  -- vecsize:_ <- getArgs
  doIt vecsize

vecsize :: Int
vecsize = 3000000000

doIt :: Int -> IO ()
doIt vecsize = do
  c <- getNumCapabilities
  defaultMain
    [env setup $ \v -> bench ("reduce (" ++ show c ++ " threads)")
                           $ nf sumStrided3 v]
  where
    setup = return $ V.replicate vecsize 99
{-
  _ <- evaluate v
  st <- getCurrentTime
  sm <- evaluate $ sumStrided3 v
  en <- getCurrentTime
  putStrLn $ "Sum: "  ++ show sm
  putStrLn $ "Time: " ++ show (diffUTCTime en st)
-}

{-
main :: IO ()
main = do
  c <- getNumCapabilities
  defaultMain
    [env setup $ \arr -> bench ("reduce (" ++ show c ++ " threads)")
                           $ nfIO $ reduce arr tILESIZE]
-}
