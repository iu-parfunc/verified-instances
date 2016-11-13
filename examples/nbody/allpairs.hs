{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

{-
File: allpairs.hs
Description: nbody computation: full all-pairs version
Original author: Prabhat Totoo
Modified by: Ryan Scott

Compile | Run
Seq: $ ghc --make -O2 -fforce-recomp allpairs.hs | allpairs <numbodies> <steps>
Par: $ ghc --make -O2 -threaded -rtsopts -fforce-recomp allpairs.hs | allpairs <numbodies> <steps> +RTS -Nx
-}
module Main (main) where

import           Control.DeepSeq
import           Control.Monad.Par

import           Criterion.Main

import           Data.List (foldl')
import qualified Data.Vector.Unboxed as V
import           Data.Vector.Unboxed (Vector, Unbox)
import           Data.Vector.Unboxed.Deriving

import           GHC.Conc (numCapabilities)

import           System.Random

-- a body consists of pos, vel and mass
data Body = Body
    { _x  :: Double   -- pos of x
    , _y  :: Double   -- pos of y
    , _z  :: Double   -- pos of z
    , _vx :: Double   -- vel of x
    , _vy :: Double   -- vel of y
    , _vz :: Double   -- vel of z
    , _m  :: Double } -- mass
    deriving Eq

$(derivingUnbox "Body"
    [t| Body -> ((Double, Double, Double), (Double, Double, Double), Double) |]
    [| \(Body x' y' z' vx' vy' vz' m') -> ((x', y', z'), (vx', vy', vz'), m') |]
    [| \((x', y', z'), (vx', vy', vz'), m') -> Body x' y' z' vx' vy' vz' m' |])

-- acceleration
data Accel = Accel
    { _ax :: {-# UNPACK #-} !Double
    , _ay :: {-# UNPACK #-} !Double
    , _az :: {-# UNPACK #-} !Double }

-- Basically Sum
instance Monoid Accel where
  mempty = Accel 0 0 0
  mappend (Accel x1 y1 z1) (Accel x2 y2 z2)
    = Accel (x1 + x2) (y1 + y2) (z1 + z2)

$(derivingUnbox "Accel"
    [t| Accel -> (Double, Double, Double) |]
    [| \(Accel ax' ay' az') -> (ax', ay', az') |]
    [| \(ax', ay', az') -> Accel ax' ay' az' |])

instance NFData Body where rnf !_ = ()
instance NFData Accel where rnf !_ = ()

-- chunksize xs = (length xs) `quot` (numCapabilities * 1)
chunksize :: Unbox a => Vector a -> Int
chunksize xs = (V.length xs) `quot` (numCapabilities * 2)
-- chunksize xs = (length xs) `quot` (numCapabilities * 4)

parMapChunk :: (Unbox a, Unbox b) => (a -> b) -> Int -> Vector a -> Par (Vector b)
parMapChunk g n xs = fmap V.concat $ parMap (V.map g) (chunk n xs)

chunk :: Unbox a => Int -> Vector a -> [Vector a]
chunk n = go
  where
    go xs | V.null xs = []
          | otherwise = as : chunk n bs where (as,bs) = V.splitAt n xs

timeStep :: Double
timeStep = 0.001

-- epsilon
eps :: Double
eps = 0.01

randomList :: Random a => Int -> [a]
randomList seed = randoms (mkStdGen seed)

genBody :: Int -> Body
genBody s = Body (rand!!1) (rand!!2) (rand!!3) (rand!!4) (rand!!5) (rand!!6) (rand!!7)
  where
    rand = randomList s

numBodies, numSteps :: Int
numBodies = 1024
numSteps  = 20

main :: IO ()
main = defaultMain
    [env (return setup) $ \ ~(bs', _) ->
        bench ("n-body (" ++ show numCapabilities ++ " threads)")
              (nf (V.foldl' f 0 . doSteps numSteps) bs')]
  where
    setup :: (Vector Body, Double)
    setup = (bs, res1)

    bs :: Vector Body
    bs = V.map genBody $ V.enumFromN 0 numBodies

    res1 :: Double
    res1 = V.foldl' f 0 bs

f :: Double -> Body -> Double
f acc (Body x' y' z' vx' vy' vz' m') = acc+x'+y'+z'+vx'+vy'+vz'+m'

seqFold :: forall a. (NFData a, Unbox a) => (a -> a -> a) -> a -> Vector a -> Par a
seqFold f z = return . V.foldl' f z

parFold :: forall a. (NFData a, Unbox a) => (a -> a -> a) -> a -> Vector a -> Par a
parFold f' z xs
    | V.null xs = return z
    | otherwise = res
  where
    parts :: [Vector a]
    parts = chunk (chunksize xs) xs

    partsRs :: Par [a]
    partsRs = parMap (V.foldl' f' z) parts

    res :: Par a
    res = fmap (foldl' f' z) partsRs

parMapFold :: (Unbox a, Monoid b, NFData b, Unbox b)
           => (b -> b -> b) -> (a -> b) -> Vector a -> b
parMapFold f' g xs = runPar $ do
  xs' <- parMapChunk g (chunksize xs) xs
  parFold f' mempty xs'

doSteps :: Int -> Vector Body -> Vector Body
doSteps 0 bs = bs
doSteps s bs = doSteps (s-1) new_bs
  where
    new_bs :: Vector Body
    new_bs = runPar $ parMapChunk (updatePos . updateVel) (chunksize bs) bs

    updatePos :: Body -> Body
    updatePos (Body x' y' z' vx' vy' vz' m') = Body (x'+timeStep*vx') (y'+timeStep*vy') (z'+timeStep*vz') vx' vy' vz' m'

    updateVel :: Body -> Body
    -- updateVel b = V.foldl' deductChange b (V.map (accel b) bs)
    updateVel b = deductChange b (parMapFold mappend (accel b) bs)

    deductChange :: Body -> Accel -> Body
    deductChange (Body x' y' z' vx' vy' vz' m') (Accel ax' ay' az') = Body x' y' z' (vx'-ax') (vy'-ay') (vz'-az') m'

    accel :: Body -> Body -> Accel
    accel b_i b_j
        | b_i == b_j = Accel 0 0 0
        | otherwise = Accel (dx*jm*mag) (dy*jm*mag) (dz*jm*mag)
      where
        mag, distance, dSquared, dx, dy, dz :: Double
        mag = timeStep / (dSquared * distance)
        distance = sqrt (dSquared)
        dSquared = dx*dx + dy*dy + dz*dz + eps
        dx = ix - jx
        dy = iy - jy
        dz = iz - jz

        Body ix iy iz _ _ _ _  = b_i
        Body jx jy jz _ _ _ jm = b_j
