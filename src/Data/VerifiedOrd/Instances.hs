{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}

module Data.VerifiedOrd.Instances (vordUnit, vordInt, module X) where

import Data.VerifiedOrd.Instances.Iso  as X
import Data.VerifiedOrd.Instances.Prod as X
import Data.VerifiedOrd.Instances.Sum  as X

import Data.VerifiedOrd
import Data.VerifiedEq.Instances
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
