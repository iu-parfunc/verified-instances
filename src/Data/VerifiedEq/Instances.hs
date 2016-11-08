{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}

module Data.VerifiedEq.Instances (veqInt, veqUnit, veqDouble, module X) where

import Data.VerifiedEq.Instances.Contra   as X
import Data.VerifiedEq.Instances.Generics as X
import Data.VerifiedEq.Instances.Iso      as X
import Data.VerifiedEq.Instances.Prod     as X
import Data.VerifiedEq.Instances.Sum      as X

import Data.VerifiedEq
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize eqUnit @-}
eqUnit :: () -> () -> Bool
eqUnit () () = True
{-# INLINE eqUnit #-}

{-@ eqUnitRefl :: x:() -> { eqUnit x x } @-}
eqUnitRefl :: () -> Proof
eqUnitRefl () = eqUnit () () ==. True *** QED

{-@ eqUnitSym :: x:() -> y:() -> { eqUnit x y ==> eqUnit y x } @-}
eqUnitSym :: () -> () -> Proof
eqUnitSym () () = eqUnit () () ==. True *** QED

{-@ eqUnitTrans :: x:() -> y:() -> z:() -> { eqUnit x y && eqUnit y z ==> eqUnit x z } @-}
eqUnitTrans :: () -> () -> () -> Proof
eqUnitTrans () () () = (eqUnit () () && eqUnit () ()) ==. True *** QED

veqUnit :: VerifiedEq ()
veqUnit = VerifiedEq eqUnit eqUnitRefl eqUnitSym eqUnitTrans

{-@ axiomatize eqInt @-}
eqInt :: Int -> Int -> Bool
eqInt x y = x == y
{-# INLINE eqInt #-}

{-@ eqIntRefl :: x:Int -> { eqInt x x } @-}
eqIntRefl :: Int -> Proof
eqIntRefl x = eqInt x x ==. x == x *** QED

{-@ eqIntSym :: x:Int -> y:Int -> { eqInt x y ==> eqInt y x } @-}
eqIntSym :: Int -> Int -> Proof
eqIntSym x y = eqInt x y ==. x == y ==. y == x *** QED

{-@ eqIntTrans :: x:Int -> y:Int -> z:Int -> { eqInt x y && eqInt y z ==> eqInt x z } @-}
eqIntTrans :: Int -> Int -> Int -> Proof
eqIntTrans x y z = (eqInt x y && eqInt y z) ==. (x == y && y == z) ==. x == z *** QED

veqInt :: VerifiedEq Int
veqInt = VerifiedEq eqInt eqIntRefl eqIntSym eqIntTrans

{-@ axiomatize eqDouble @-}
eqDouble :: Double -> Double -> Bool
eqDouble x y = x == y
{-# INLINE eqDouble #-}

{-@ eqDoubleRefl :: x:Double -> { eqDouble x x } @-}
eqDoubleRefl :: Double -> Proof
eqDoubleRefl x = eqDouble x x ==. x == x *** QED

{-@ eqDoubleSym :: x:Double -> y:Double
                -> { eqDouble x y ==> eqDouble y x } @-}
eqDoubleSym :: Double -> Double -> Proof
eqDoubleSym x y = eqDouble x y ==. x == y ==. y == x *** QED

{-@ eqDoubleTrans :: x:Double -> y:Double -> z:Double
                  -> { eqDouble x y && eqDouble y z ==> eqDouble x z } @-}
eqDoubleTrans :: Double -> Double -> Double -> Proof
eqDoubleTrans x y z
  =   (eqDouble x y && eqDouble y z)
  ==. (x == y       && y == z)
  ==. x == z
  *** QED

veqDouble :: VerifiedEq Double
veqDouble = VerifiedEq eqDouble eqDoubleRefl eqDoubleSym eqDoubleTrans
