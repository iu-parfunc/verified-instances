{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}

module Data.VerifiedOrd.Instances (vordUnit, vordInt, vordDouble, module X) where

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

{-@ leqUnitTotal :: x:() -> y:() -> { leqUnit x y || leqUnit y x } @-}
leqUnitTotal :: () -> () -> Proof
leqUnitTotal () () = (leqUnit () () || leqUnit () ()) ==. True *** QED

{-@ leqUnitAntisym :: x:() -> y:() -> { leqUnit x y && leqUnit y x ==> x == y } @-}
leqUnitAntisym :: () -> () -> Proof
leqUnitAntisym () () = (leqUnit () () && leqUnit () ()) ==. True *** QED

{-@ leqUnitTrans :: x:() -> y:() -> z:() -> { leqUnit x y && leqUnit y z ==> leqUnit x z } @-}
leqUnitTrans :: () -> () -> () -> Proof
leqUnitTrans () () () = (leqUnit () () && leqUnit () ()) ==. True *** QED

vordUnit :: VerifiedOrd ()
vordUnit = VerifiedOrd leqUnit leqUnitTotal leqUnitAntisym leqUnitTrans veqUnit

{-@ axiomatize leqInt @-}
leqInt :: Int -> Int -> Bool
leqInt x y = x <= y
{-# INLINE leqInt #-}

{-@ leqIntTotal :: x:Int -> y:Int -> { leqInt x y || leqInt y x } @-}
leqIntTotal :: Int -> Int -> Proof
leqIntTotal x y = (leqInt x y || leqInt y x) ==. (x <= y || y <= x) *** QED

{-@ leqIntAntisym :: x:Int -> y:Int -> { leqInt x y && leqInt y x ==> x == y } @-}
leqIntAntisym :: Int -> Int -> Proof
leqIntAntisym x y = (leqInt x y && leqInt y x) ==. (x <= y && y <= x) ==. x == y *** QED

{-@ leqIntTrans :: x:Int -> y:Int -> z:Int -> { leqInt x y && leqInt y z ==> leqInt x z } @-}
leqIntTrans :: Int -> Int -> Int -> Proof
leqIntTrans x y z = (leqInt x y && leqInt y z) ==. (x <= y && y <= z) ==. x <= z ==. leqInt x z *** QED

vordInt :: VerifiedOrd Int
vordInt = VerifiedOrd leqInt leqIntTotal leqIntAntisym leqIntTrans veqInt

{-@ axiomatize leqDouble @-}
leqDouble :: Double -> Double -> Bool
leqDouble x y = x <= y
{-# INLINE leqDouble #-}

{-@ leqDoubleTotal :: x:Double -> y:Double
                   -> { leqDouble x y || leqDouble y x } @-}
leqDoubleTotal :: Double -> Double -> Proof
leqDoubleTotal x y
  =   (leqDouble x y || leqDouble y x)
  ==. (x <= y || y <= x)
  *** QED

{-@ leqDoubleAntisym :: x:Double -> y:Double
                     -> { leqDoule x y && leqDouble y x ==> x == y } @-}
leqDoubleAntisym :: Double -> Double -> Proof
leqDoubleAntisym x y
  =   (leqDouble x y && leqDouble y x)
  ==. (x <= y && y <= x)
  ==. x == y
  *** QED

{-@ leqDoubleTrans :: x:Double -> y:Double -> z:Double
 -                 -> { leqDouble x y && leqDouble y z ==> leqDouble x z } @-}
leqDoubleTrans :: Double -> Double -> Double -> Proof
leqDoubleTrans x y z
  =   (leqDouble x y && leqDouble y z)
  ==. (x <= y && y <= z)
  ==. x <= z
  ==. leqDouble x z
  *** QED

vordDouble :: VerifiedOrd Double
vordDouble = VerifiedOrd leqDouble leqDoubleTotal
                         leqDoubleAntisym leqDoubleTrans veqDouble
