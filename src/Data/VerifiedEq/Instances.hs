{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}

module Data.VerifiedEq.Instances (veqInt, veqUnit, module X) where

import Data.VerifiedEq.Instances.Contra as X
import Data.VerifiedEq.Instances.Iso    as X
import Data.VerifiedEq.Instances.Prod   as X
import Data.VerifiedEq.Instances.Sum    as X

import Data.VerifiedEq
import GHC.Generics
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

{-@ data V1 @-}

{-@ axiomatize eqV1 @-}
eqV1 :: V1 p -> V1 p -> Bool
eqV1 _ _ = True

{-@ eqV1Refl :: x:V1 p -> { eqV1 x x } @-}
eqV1Refl :: V1 p -> Proof
eqV1Refl x = eqV1 x x *** QED

{-@ eqV1Sym :: x:V1 p -> y:V1 p -> { eqV1 x y ==> eqV1 y x } @-}
eqV1Sym :: V1 p -> V1 p -> Proof
eqV1Sym x y = eqV1 x y ==. eqV1 y x *** QED

{-@ eqV1Trans :: x:V1 p -> y:V1 p -> z:V1 p -> { eqV1 x y && eqV1 y z ==> eqV1 x z } @-}
eqV1Trans :: V1 p -> V1 p -> V1 p -> Proof
eqV1Trans x y z = (eqV1 x y && eqV1 y z) ==. eqV1 x z *** QED

veqV1 :: VerifiedEq (V1 p)
veqV1 = VerifiedEq eqV1 eqV1Refl eqV1Sym eqV1Trans

{-@ data U1 p = U1 @-}

{-@ axiomatize eqU1 @-}
eqU1 :: U1 p -> U1 p -> Bool
eqU1 _ _ = True

{-@ eqU1Refl :: x:U1 p -> { eqU1 x x } @-}
eqU1Refl :: U1 p -> Proof
eqU1Refl x = eqU1 x x *** QED

{-@ eqU1Sym :: x:U1 p -> y:U1 p -> { eqU1 x y ==> eqU1 y x } @-}
eqU1Sym :: U1 p -> U1 p -> Proof
eqU1Sym x y = eqU1 x y ==. eqU1 y x *** QED

{-@ eqU1Trans :: x:U1 p -> y:U1 p -> z:U1 p -> { eqU1 x y && eqU1 y z ==> eqU1 x z } @-}
eqU1Trans :: U1 p -> U1 p -> U1 p -> Proof
eqU1Trans x y z = (eqU1 x y && eqU1 y z) ==. eqU1 x z *** QED

veqU1 :: VerifiedEq (U1 p)
veqU1 = VerifiedEq eqU1 eqU1Refl eqU1Sym eqU1Trans

{-@ newtype Par1 p = Par1 { unPar1 :: p } @-}

{-@ axiomatize eqPar1 @-}
eqPar1 :: (p -> p -> Bool) -> Par1 p -> Par1 p -> Bool
eqPar1 eqP x y = eqP (unPar1 x) (unPar1 y)

{-@ eqPar1Refl :: eqP:(p -> p -> Bool) -> eqPRefl:(x:p -> { Prop (eqP x x) })
	       -> x:Par1 p -> { eqPar1 eqP x x } @-}
eqPar1Refl :: (p -> p -> Bool) -> (p -> Proof) -> Par1 p -> Proof
eqPar1Refl eqP eqPRefl x
  =   eqPar1 eqP x x
  ==. eqP (unPar1 x) (unPar1 x)
  ==. True ? eqPRefl (unPar1 x)
  *** QED

{-@ eqPar1Sym :: eqP:(p -> p -> Bool) -> eqPSym:(x:p -> y:p -> { Prop (eqP x y) ==> Prop (eqP y x) })
	      -> x:Par1 p -> y:Par1 p -> { eqPar1 eqP x y ==> eqPar1 eqP y x } @-}
eqPar1Sym :: (p -> p -> Bool) -> (p -> p -> Proof)
          -> Par1 p -> Par1 p -> Proof
eqPar1Sym eqP eqPSym x y
  =   eqPar1 eqP x y
  ==. eqP (unPar1 x) (unPar1 y)
  ==. eqP (unPar1 y) (unPar1 x) ? eqPSym (unPar1 x) (unPar1 y)
  ==. eqPar1 eqP y x
  *** QED

{-@ eqPar1Trans :: eqP:(p -> p -> Bool) -> eqPTrans:(x:p -> y:p -> z:p -> { Prop (eqP x y) && Prop (eqP y z) ==> Prop (eqP x z) })
		-> x:Par1 p -> y:Par1 p -> z:Par1 p -> { eqPar1 eqP x y && eqPar1 eqP y z ==> eqPar1 eqP x z } @-}
eqPar1Trans :: (p -> p -> Bool) -> (p -> p -> p -> Proof)
	    -> Par1 p -> Par1 p -> Par1 p -> Proof
eqPar1Trans eqP eqPTrans x y z
  =   (eqPar1 eqP x y && eqPar1 eqP y z)
  ==. (eqP (unPar1 x) (unPar1 y) && eqP (unPar1 y) (unPar1 z))
  ==. eqP (unPar1 x) (unPar1 z) ? eqPTrans (unPar1 x) (unPar1 y) (unPar1 z)
  ==. eqPar1 eqP x z
  *** QED

veqPar1 :: VerifiedEq p -> VerifiedEq (Par1 p)
veqPar1 (VerifiedEq eqP eqPRefl eqPSym eqPTrans)
  = VerifiedEq (eqPar1 eqP)
	       (eqPar1Refl eqP eqPRefl)
	       (eqPar1Sym eqP eqPSym)
	       (eqPar1Trans eqP eqPTrans)

{-
{-@ data (:+:) f g p = L1 (f p) | R1 (g p) @-}

{-@ axiomatize eqSum @-}
eqSum :: (f p -> f p -> Bool) -> (g p -> g p -> Bool)
      -> (:+:) f g p -> (:+:) f g p -> Bool
eqSum eqFp _    (L1 x) (L1 y) = eqFp x y
eqSum _    eqGp (R1 x) (R1 y) = eqGp x y
eqSum _    _    (L1 _) (R1 _) = False
eqSum _    _    (R1 _) (L1 _) = False
-}
