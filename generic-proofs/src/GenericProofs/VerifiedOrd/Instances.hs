{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
module GenericProofs.VerifiedOrd.Instances (vordUnit, vordInt, vordInt64, vordDouble) where

import Data.Int
import GenericProofs.VerifiedOrd
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize leqUnit @-}
leqUnit :: () -> () -> Bool
leqUnit () () = True
{-# INLINE leqUnit #-}

{-@ leqUnitRefl :: x:() -> { leqUnit x x } @-}
leqUnitRefl :: () -> Proof
leqUnitRefl () = leqUnit () () ==. True *** QED

{-@ leqUnitAntisym :: x:() -> y:() -> { leqUnit x y && leqUnit y x ==> x == y } @-}
leqUnitAntisym :: () -> () -> Proof
leqUnitAntisym () () = (leqUnit () () && leqUnit () ()) ==. True *** QED

{-@ leqUnitTrans :: x:() -> y:() -> z:() -> { leqUnit x y && leqUnit y z ==> leqUnit x z } @-}
leqUnitTrans :: () -> () -> () -> Proof
leqUnitTrans () () () = (leqUnit () () && leqUnit () ()) ==. True *** QED

{-@ leqUnitTotal :: x:() -> y:() -> { leqUnit x y || leqUnit y x } @-}
leqUnitTotal :: () -> () -> Proof
leqUnitTotal () () = (leqUnit () () || leqUnit () ()) ==. True *** QED

vordUnit :: VerifiedOrd ()
vordUnit = VerifiedOrd leqUnit leqUnitRefl leqUnitAntisym leqUnitTrans leqUnitTotal

{-@ axiomatize leqInt @-}
leqInt :: Int -> Int -> Bool
leqInt x y = x <= y
{-# INLINE leqInt #-}

{-@ leqIntRefl :: x:Int -> { leqInt x x } @-}
leqIntRefl :: Int -> Proof
leqIntRefl x = leqInt x x ==. x <= x *** QED

{-@ leqIntAntisym :: x:Int -> y:Int -> { leqInt x y && leqInt y x ==> x == y } @-}
leqIntAntisym :: Int -> Int -> Proof
leqIntAntisym x y = (leqInt x y && leqInt y x) ==. (x <= y && y <= x) ==. x == y *** QED

{-@ leqIntTrans :: x:Int -> y:Int -> z:Int -> { leqInt x y && leqInt y z ==> leqInt x z } @-}
leqIntTrans :: Int -> Int -> Int -> Proof
leqIntTrans x y z = (leqInt x y && leqInt y z) ==. (x <= y && y <= z) ==. x <= z ==. leqInt x z *** QED

{-@ leqIntTotal :: x:Int -> y:Int -> { leqInt x y || leqInt y x } @-}
leqIntTotal :: Int -> Int -> Proof
leqIntTotal x y = (leqInt x y || leqInt y x) ==. (x <= y || y <= x) *** QED

vordInt :: VerifiedOrd Int
vordInt = VerifiedOrd leqInt leqIntRefl leqIntAntisym leqIntTrans leqIntTotal

{-@ axiomatize leqInt64 @-}
leqInt64 :: Int64 -> Int64 -> Bool
leqInt64 x y = x <= y
{-# INLINE leqInt64 #-}

{-@ leqInt64Refl :: x:Int64 -> { leqInt64 x x } @-}
leqInt64Refl :: Int64 -> Proof
leqInt64Refl x = leqInt64 x x ==. x <= x *** QED

{-@ leqInt64Antisym :: x:Int64 -> y:Int64 -> { leqInt64 x y && leqInt64 y x ==> x == y } @-}
leqInt64Antisym :: Int64 -> Int64 -> Proof
leqInt64Antisym x y = (leqInt64 x y && leqInt64 y x) ==. (x <= y && y <= x) ==. x == y *** QED

{-@ leqInt64Trans :: x:Int64 -> y:Int64 -> z:Int64 -> { leqInt64 x y && leqInt64 y z ==> leqInt64 x z } @-}
leqInt64Trans :: Int64 -> Int64 -> Int64 -> Proof
leqInt64Trans x y z = (leqInt64 x y && leqInt64 y z) ==. (x <= y && y <= z) ==. x <= z ==. leqInt64 x z *** QED

{-@ leqInt64Total :: x:Int64 -> y:Int64 -> { leqInt64 x y || leqInt64 y x } @-}
leqInt64Total :: Int64 -> Int64 -> Proof
leqInt64Total x y = (leqInt64 x y || leqInt64 y x) ==. (x <= y || y <= x) *** QED

vordInt64 :: VerifiedOrd Int64
vordInt64 = VerifiedOrd leqInt64 leqInt64Refl leqInt64Antisym leqInt64Trans leqInt64Total

{-@ axiomatize leqDouble @-}
leqDouble :: Double -> Double -> Bool
leqDouble x y = x <= y
{-# INLINE leqDouble #-}

{-@ leqDoubleRefl :: x:Double -> { leqDouble x x } @-}
leqDoubleRefl :: Double -> Proof
leqDoubleRefl x = leqDouble x x ==. x <= x *** QED

{-@ leqDoubleTotal :: x:Double -> y:Double
                   -> { leqDouble x y || leqDouble y x } @-}
leqDoubleTotal :: Double -> Double -> Proof
leqDoubleTotal x y
  =   (leqDouble x y || leqDouble y x)
  ==. (x <= y || y <= x)
  *** QED

{-@ leqDoubleAntisym :: x:Double -> y:Double
                     -> { leqDouble x y && leqDouble y x ==> x == y } @-}
leqDoubleAntisym :: Double -> Double -> Proof
leqDoubleAntisym x y
  =   (leqDouble x y && leqDouble y x)
  ==. (x <= y && y <= x)
  ==. x == y
  *** QED

{-@ leqDoubleTrans :: x:Double -> y:Double -> z:Double
                   -> { leqDouble x y && leqDouble y z ==> leqDouble x z } @-}
leqDoubleTrans :: Double -> Double -> Double -> Proof
leqDoubleTrans x y z
  =   (leqDouble x y && leqDouble y z)
  ==. (x <= y && y <= z)
  ==. x <= z
  ==. leqDouble x z
  *** QED

vordDouble :: VerifiedOrd Double
vordDouble = VerifiedOrd leqDouble leqDoubleRefl leqDoubleAntisym
                         leqDoubleTrans leqDoubleTotal
