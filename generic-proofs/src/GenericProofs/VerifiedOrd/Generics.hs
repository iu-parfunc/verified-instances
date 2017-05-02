{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE EmptyCase #-}
module GenericProofs.VerifiedOrd.Generics where

import GenericProofs.VerifiedOrd
import Generics.Deriving.Newtypeless
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize leqU1 @-}
leqU1 :: U1 p -> U1 p -> Bool
leqU1 _ _ = True

{-@ leqU1Refl :: x:U1 p -> { leqU1 x x } @-}
leqU1Refl :: U1 p -> Proof
leqU1Refl U1 = leqU1 U1 U1 ==. True *** QED

{-@ leqU1Antisym :: x:U1 p -> y:U1 p -> { leqU1 x y && leqU1 y x ==> x == y } @-}
leqU1Antisym :: U1 p -> U1 p -> Proof
leqU1Antisym U1 U1 = (leqU1 U1 U1 && leqU1 U1 U1) ==. True ==. (U1 == U1) *** QED

{-@ leqU1Trans :: x:U1 p -> y:U1 p -> z:U1 p -> { leqU1 x y && leqU1 y z ==> leqU1 x z } @-}
leqU1Trans :: U1 p -> U1 p -> U1 p -> Proof
leqU1Trans U1 U1 U1 = (leqU1 U1 U1 && leqU1 U1 U1) ==. True ==. leqU1 U1 U1 *** QED

{-@ leqU1Total :: x:U1 p -> y:U1 p -> { leqU1 x y || leqU1 y x } @-}
leqU1Total :: U1 p -> U1 p -> Proof
leqU1Total U1 U1 = (leqU1 U1 U1 || leqU1 U1 U1) ==. True *** QED

vordU1 :: VerifiedOrd (U1 p)
vordU1 = VerifiedOrd leqU1 leqU1Refl leqU1Antisym leqU1Trans leqU1Total
