{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Data.VerifiedOrd.Instances
  ( vordUnit
  , vordInt
  , vordInt64
  , vordDouble
  , module X
  , leqUnit
  , leqInt
  , leqInt64
  , leqDouble )
  where

import Data.Int

import Data.VerifiedOrd.Instances.Inj           as X
import Data.VerifiedOrd.Instances.Iso           as X
import Data.VerifiedOrd.Instances.Prod          as X
import Data.VerifiedOrd.Instances.Sum           as X

import Data.VerifiedEq.Instances
import Data.VerifiedOrd
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize leqUnit @-}
leqUnit :: () -> () -> Bool
leqUnit () () = True
{-# INLINE leqUnit #-}

{-@ leqUnitRefl :: x:() -> { leqUnit x x } @-}
leqUnitRefl :: () -> Proof
leqUnitRefl () = simpleProof

{-@ leqUnitAntisym :: x:() -> y:{() | leqUnit x y && leqUnit y x} -> {x == y} @-}
leqUnitAntisym :: () -> () -> Proof
leqUnitAntisym () () = simpleProof

{-@ leqUnitTrans :: x:() -> y:{() | leqUnit x y} -> z:{() | leqUnit y z} -> {leqUnit x z} @-}
leqUnitTrans :: () -> () -> () -> Proof
leqUnitTrans () () () = simpleProof

{-@ leqUnitTotal :: x:() -> y:() -> {leqUnit x y || leqUnit y x} @-}
leqUnitTotal :: () -> () -> Proof
leqUnitTotal () () = (leqUnit () () || leqUnit () ()) *** QED

vordUnit :: VerifiedOrd ()
vordUnit = VerifiedOrd leqUnit leqUnitRefl leqUnitAntisym leqUnitTrans leqUnitTotal veqUnit

{-@ axiomatize leqInt @-}
leqInt :: Int -> Int -> Bool
leqInt x y = x <= y
{-# INLINE leqInt #-}

{-@ leqIntRefl :: x:Int -> { leqInt x x } @-}
leqIntRefl :: Int -> Proof
leqIntRefl x = simpleProof

{-@ leqIntAntisym :: x:Int -> y:{Int | leqInt x y && leqInt y x} -> {x == y} @-}
leqIntAntisym :: Int -> Int -> Proof
leqIntAntisym x y = simpleProof

{-@ leqIntTrans :: x:Int -> y:{Int | leqInt x y} -> z:{Int | leqInt y z} -> {leqInt x z} @-}
leqIntTrans :: Int -> Int -> Int -> Proof
leqIntTrans x y z = simpleProof

{-@ leqIntTotal :: x:Int -> y:Int -> { leqInt x y || leqInt y x } @-}
leqIntTotal :: Int -> Int -> Proof
leqIntTotal x y = (leqInt x y || leqInt y x) *** QED

vordInt :: VerifiedOrd Int
vordInt = VerifiedOrd leqInt leqIntRefl leqIntAntisym leqIntTrans leqIntTotal veqInt

{-@ axiomatize leqInt64 @-}
leqInt64 :: Int64 -> Int64 -> Bool
leqInt64 x y = x <= y
{-# INLINE leqInt64 #-}

{-@ leqInt64Refl :: x:Int64 -> { leqInt64 x x } @-}
leqInt64Refl :: Int64 -> Proof
leqInt64Refl x = simpleProof

{-@ leqInt64Antisym :: x:Int64 -> y:{Int64 | leqInt64 x y && leqInt64 y x} -> {x == y} @-}
leqInt64Antisym :: Int64 -> Int64 -> Proof
leqInt64Antisym x y = simpleProof

{-@ leqInt64Trans :: x:Int64 -> y:{Int64 | leqInt64 x y} -> z:{Int64 | leqInt64 y z} -> {leqInt64 x z} @-}
leqInt64Trans :: Int64 -> Int64 -> Int64 -> Proof
leqInt64Trans x y z = simpleProof

{-@ leqInt64Total :: x:Int64 -> y:Int64 -> { leqInt64 x y || leqInt64 y x } @-}
leqInt64Total :: Int64 -> Int64 -> Proof
leqInt64Total x y = (leqInt64 x y || leqInt64 y x) *** QED

vordInt64 :: VerifiedOrd Int64
vordInt64 = VerifiedOrd leqInt64 leqInt64Refl leqInt64Antisym leqInt64Trans leqInt64Total veqInt64

{-@ axiomatize leqDouble @-}
leqDouble :: Double -> Double -> Bool
leqDouble x y = x <= y
{-# INLINE leqDouble #-}

{-@ leqDoubleRefl :: x:Double -> { leqDouble x x } @-}
leqDoubleRefl :: Double -> Proof
leqDoubleRefl x = simpleProof

{-@ leqDoubleTotal :: x:Double -> y:Double
                   -> { leqDouble x y || leqDouble y x } @-}
leqDoubleTotal :: Double -> Double -> Proof
leqDoubleTotal x y = (leqDouble x y || leqDouble y x) *** QED

{-@ leqDoubleAntisym :: x:Double -> y:{Double | leqDouble x y && leqDouble y x}
                     -> {x == y} @-}
leqDoubleAntisym :: Double -> Double -> Proof
leqDoubleAntisym x y = simpleProof

{-@ leqDoubleTrans :: x:Double -> y:{Double | leqDouble x y} -> z:{Double | leqDouble y z}
                   -> {leqDouble x z} @-}
leqDoubleTrans :: Double -> Double -> Double -> Proof
leqDoubleTrans x y z = simpleProof

vordDouble :: VerifiedOrd Double
vordDouble = VerifiedOrd leqDouble leqDoubleRefl leqDoubleAntisym
                         leqDoubleTrans leqDoubleTotal veqDouble
