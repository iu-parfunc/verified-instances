{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--prune-unsorted"     @-}
{-# LANGUAGE EmptyCase #-}

module Data.VerifiedOrd.Instances.Generics where

import Data.VerifiedEq.Instances.Generics       (absurd, veqU1, veqV1)
import Data.VerifiedOrd
import GHC.Generics
import Language.Haskell.Liquid.ProofCombinators

{-@ measure elimV1 @-}
elimV1 :: V1 p -> Bool
elimV1 x = case x of {}

{-@ axiomatize leqV1 @-}
leqV1 :: V1 p -> V1 p -> Bool
leqV1 x _ = elimV1 x

vordV1 :: VerifiedOrd (V1 p)
vordV1 = VerifiedOrd leqV1 absurd (\_ -> absurd) (\_ _ -> absurd) (\_ -> absurd) veqV1

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
vordU1 = VerifiedOrd leqU1 leqU1Refl leqU1Antisym leqU1Trans leqU1Total veqU1

{-@ axiomatize leqPar1 @-}
leqPar1 :: (p -> p -> Bool) -> Par1 p -> Par1 p -> Bool
leqPar1 leqP x y = leqP (unPar1 x) (unPar1 y)

{-@ leqPar1Refl :: leqP:(p -> p -> Bool) -> leqPRefl:(x:p -> { leqP x x })
                -> x:Par1 p -> { leqPar1 leqP x x } @-}
leqPar1Refl :: (p -> p -> Bool) -> (p -> Proof) -> Par1 p -> Proof
leqPar1Refl leqP leqPRefl x
  =   leqPar1 leqP x x
  ==. leqP (unPar1 x) (unPar1 x)
  ==. True ? leqPRefl (unPar1 x)
  *** QED

{-@ leqPar1Antisym :: leqP:(p -> p -> Bool) -> leqPAntisym:(x:p -> y:p -> { leqP x y ==> leqP y x })
                  -> x:Par1 p -> y:Par1 p -> { leqPar1 leqP x y ==> leqPar1 leqP y x } @-}
leqPar1Antisym :: (p -> p -> Bool) -> (p -> p -> Proof)
               -> Par1 p -> Par1 p -> Proof
leqPar1Antisym leqP leqPAntisym x y
  =   leqPar1 leqP x y
  ==. leqP (unPar1 x) (unPar1 y)
  ==. leqP (unPar1 y) (unPar1 x) ? leqPAntisym (unPar1 x) (unPar1 y)
  ==. leqPar1 leqP y x
  *** QED

{-@ leqPar1Trans :: leqP:(p -> p -> Bool) -> leqPTrans:(x:p -> y:p -> z:p -> { leqP x y && leqP y z ==> leqP x z })
                 -> x:Par1 p -> y:Par1 p -> z:Par1 p -> { leqPar1 leqP x y && leqPar1 leqP y z ==> leqPar1 leqP x z } @-}
leqPar1Trans :: (p -> p -> Bool) -> (p -> p -> p -> Proof)
             -> Par1 p -> Par1 p -> Par1 p -> Proof
leqPar1Trans leqP leqPTrans x y z
  =   (leqPar1 leqP x y && leqPar1 leqP y z)
  ==. (leqP (unPar1 x) (unPar1 y) && leqP (unPar1 y) (unPar1 z))
  ==. leqP (unPar1 x) (unPar1 z) ? leqPTrans (unPar1 x) (unPar1 y) (unPar1 z)
  ==. leqPar1 leqP x z
  *** QED
