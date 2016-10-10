{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}

module Data.VerifiedOrd.Instances (vordInt) where

import Data.VerifiedOrd
import Data.VerifiedEq.Instances
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize leqInt @-}
leqInt :: Int -> Int -> Bool
leqInt x y = x <= y

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
