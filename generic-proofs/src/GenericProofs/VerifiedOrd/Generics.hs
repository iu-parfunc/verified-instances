{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE EmptyCase #-}
module GenericProofs.VerifiedOrd.Generics where

import GenericProofs.VerifiedOrd
import Generics.Deriving.Newtypeless.Base.Internal
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

{-@ axiomatize leqK1 @-}
leqK1 :: (c -> c -> Bool) -> K1 i c p -> K1 i c p -> Bool
leqK1 leqC (K1 c1) (K1 c2) = leqC c1 c2

{-@ leqK1Refl :: leqC:(c -> c -> Bool)
              -> leqCRefl:(x:c -> { leqC x x })
              -> x:K1 i c p
              -> { leqK1 leqC x x }
@-}
leqK1Refl :: (c -> c -> Bool) -> (c -> Proof)
          -> K1 i c p -> Proof
leqK1Refl leqC leqCRefl x@(K1 c)
  =   leqK1 leqC x x
  ==. leqC c c
  ==. True ? leqCRefl c
  *** QED

{-
{-@ leqK1Antisym :: leqC:(c -> c -> Bool)
			     -> leqCAntisym:(x:c -> y:c -> { leqC x y && leqC y x ==> x == y })
                 -> x:K1 i c p
				 -> y:K1 i c p
				 -> { leqK1 leqC x y && leqK1 leqC y x ==> x == y }
@-}
leqK1Antisym :: (c -> c -> Bool)
             -> (c -> c -> Proof)
             -> K1 i c p
             -> K1 i c p
             -> Proof
leqK1Antisym leqC leqCAntisym x@(K1 c1) y@(K1 c2)
  =   (leqK1 leqC x y && leqK1 leqC y x)
  ==. (leqC c1 c2 && leqC c2 c1)
  ==. (c1 == c2) ? leqCAntisym c1 c2
  ==. (x == y)
  *** QED
-}

{-@ leqK1Trans :: leqC:(c -> c -> Bool)
               -> leqCTrans:(x:c -> y:c -> z:c -> { leqC x y && leqC y z ==> leqC x z })
               -> x:K1 i c p
               -> y:K1 i c p
               -> z:K1 i c p
               -> { leqK1 leqC x y && leqK1 leqC y z ==> leqK1 leqC x z } @-}
leqK1Trans :: (c -> c -> Bool)
           -> (c -> c -> c -> Proof)
           -> K1 i c p
           -> K1 i c p
           -> K1 i c p
           -> Proof
leqK1Trans leqC leqCTrans x@(K1 c1) y@(K1 c2) z@(K1 c3)
  =   (leqK1 leqC x y && leqK1 leqC y z)
  ==. (leqC c1 c2 && leqC c2 c3)
  ==. leqC c1 c3 ? leqCTrans c1 c2 c3
  ==. leqK1 leqC x z
  *** QED

{-@ leqK1Total :: leqC:(c -> c -> Bool)
               -> leqCTrans:(x:c -> y:c -> { leqC x y || leqC y x })
               -> x:K1 i c p
               -> y:K1 i c p
               -> { leqK1 leqC x y || leqK1 leqC y x }
@-}
leqK1Total :: (c -> c -> Bool)
           -> (c -> c -> Proof)
           -> K1 i c p
           -> K1 i c p
           -> Proof
leqK1Total leqC leqCTotal x@(K1 c1) y@(K1 c2)
  =   (leqK1 leqC x y || leqK1 leqC y x)
  ==. (leqC c1 c2 || leqC c2 c1)
  ==. True ? leqCTotal c1 c2
  *** QED

{-
vordK1 :: VerifiedOrd c -> VerifiedOrd (K1 i c p)
vordK1 (VerifiedOrd leqC leqCRefl leqCAntisym leqCTrans leqCTotal)
  = VerifiedOrd (leqK1 leqC)
                (leqK1Refl leqC leqCRefl)
                (leqK1Antisym leqC leqCAntisym)
                (leqK1Trans leqC leqCTrans)
                (leqK1Total leqC leqCTotal)
-}

{-@ axiomatize leqM1 @-}
leqM1 :: (f p -> f p -> Bool) -> M1 i c f p -> M1 i c f p -> Bool
leqM1 leqFP (M1 m1) (M1 m2) = leqFP m1 m2

{-@ leqM1Refl :: leqFP:(f p -> f p -> Bool)
              -> leqFPRefl:(x:(f p) -> { leqFP x x })
              -> x:M1 i c f p
              -> { leqM1 leqFP x x }
@-}
leqM1Refl :: (f p -> f p -> Bool) -> (f p -> Proof)
          -> M1 i c f p -> Proof
leqM1Refl leqFP leqFPRefl x@(M1 m)
  =   leqM1 leqFP x x
  ==. leqFP m m
  ==. True ? leqFPRefl m
  *** QED

{-
{-@ leqM1Antisym :: leqFP:(f p -> f p -> Bool)
                 -> leqFPAntisym:(x:(f p) -> y:(f p) -> { leqFP x y ==> leqFP y x })
                 -> x:M1 i c f p
                 -> y:M1 i c f p
                 -> { leqM1 leqFP x y ==> leqM1 leqFP y x }
@-}
leqM1Antisym :: (f p -> f p -> Bool)
             -> (f p -> f p -> Proof)
             -> M1 i c f p
             -> M1 i c f p
             -> Proof
leqM1Antisym leqFP leqFPAntisym x@(M1 m1) y@(M1 m2)
  =   leqM1 leqFP x y
  ==. leqFP m1 m2
  ==. leqFP m2 m1 ? leqFPAntisym m1 m2
  ==. leqM1 leqFP y x
  *** QED
-}

{-@ leqM1Trans :: leqFP:(f p -> f p -> Bool)
               -> leqFPTrans:(x:(f p) -> y:(f p) -> z:(f p) -> { leqFP x y && leqFP y z ==> leqFP x z     })
               -> x:M1 i c f p
               -> y:M1 i c f p
               -> z:M1 i c f p
               -> { leqM1 leqFP x y && leqM1 leqFP y z ==> leqM1 leqFP x z } @-}
leqM1Trans :: (f p -> f p -> Bool)
           -> (f p -> f p -> f p -> Proof)
           -> M1 i c f p
           -> M1 i c f p
           -> M1 i c f p
           -> Proof
leqM1Trans leqFP leqFPTrans x@(M1 m1) y@(M1 m2) z@(M1 m3)
  =   (leqM1 leqFP x y && leqM1 leqFP y z)
  ==. (leqFP m1 m2 && leqFP m2 m3)
  ==. leqFP m1 m3 ? leqFPTrans m1 m2 m3
  ==. leqM1 leqFP x z
  *** QED
