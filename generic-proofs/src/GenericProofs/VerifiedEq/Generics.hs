{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-# LANGUAGE EmptyCase            #-}
module GenericProofs.VerifiedEq.Generics where

import GenericProofs.Combinators
import GenericProofs.VerifiedEq
import GHC.Generics

{-@ data V1 @-}

{-@ axiomatize eqV1 @-}
eqV1 :: V1 p -> V1 p -> Bool
-- Sadly, LH barfs on this definition. We'd need to put it in a measure,
-- but measures can't return Bool!
-- eqV1 x _ = elimV1 x
eqV1 _ _ = True

absurd :: V1 p -> a
absurd x = case x of {}

{-@ eqV1Refl :: x:V1 p -> { eqV1 x x } @-}
eqV1Refl :: V1 p -> Proof
eqV1Refl x = absurd x

{-@ eqV1Sym :: x:V1 p -> y:V1 p -> { eqV1 x y ==> eqV1 y x } @-}
eqV1Sym :: V1 p -> V1 p -> Proof
eqV1Sym x _ = absurd x

{-@ eqV1Trans :: x:V1 p -> y:V1 p -> z:V1 p -> { eqV1 x y && eqV1 y z ==> eqV1 x z } @-}
eqV1Trans :: V1 p -> V1 p -> V1 p -> Proof
eqV1Trans x _ _ = absurd x

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

{-@ eqPar1Refl :: eqP:(p -> p -> Bool) -> eqPRefl:(x:p -> { eqP x x })
            -> x:Par1 p -> { eqPar1 eqP x x } @-}
eqPar1Refl :: (p -> p -> Bool) -> (p -> Proof) -> Par1 p -> Proof
eqPar1Refl eqP eqPRefl x
  =   eqPar1 eqP x x
  ==. eqP (unPar1 x) (unPar1 x)
  ==. True ? eqPRefl (unPar1 x)
  *** QED

{-@ eqPar1Sym :: eqP:(p -> p -> Bool) -> eqPSym:(x:p -> y:p -> { eqP x y ==> eqP y x })
           -> x:Par1 p -> y:Par1 p -> { eqPar1 eqP x y ==> eqPar1 eqP y x } @-}
eqPar1Sym :: (p -> p -> Bool) -> (p -> p -> Proof)
          -> Par1 p -> Par1 p -> Proof
eqPar1Sym eqP eqPSym x y
  =   eqPar1 eqP x y
  ==. eqP (unPar1 x) (unPar1 y)
  ==. eqP (unPar1 y) (unPar1 x) ? eqPSym (unPar1 x) (unPar1 y)
  ==. eqPar1 eqP y x
  *** QED

{-@ eqPar1Trans :: eqP:(p -> p -> Bool) -> eqPTrans:(x:p -> y:p -> z:p -> { eqP x y && eqP y z ==> eqP x z })
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
