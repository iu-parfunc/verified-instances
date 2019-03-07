{-@ LIQUID "--reflection"        @-}

{-# LANGUAGE EmptyCase            #-}

module Data.VerifiedEq.Instances.Generics where

import GHC.Generics hiding (unPar1)
import Data.VerifiedEq
import Language.Haskell.Liquid.ProofCombinators


{-@ reflect eqV1 @-}
eqV1 :: V1 p -> V1 p -> Bool
eqV1 _ _ = False
-- eqV1 x _ = case x of {}

absurd :: V1 p -> a
absurd x = case x of {}

{-@ eqV1Refl :: x:_ -> { eqV1 x x } @-}
eqV1Refl :: V1 p -> Proof
eqV1Refl x = absurd x

{-@ eqV1Sym :: x:_ -> y:_ -> { eqV1 x y ==> eqV1 y x } @-}
eqV1Sym :: V1 p -> V1 p -> Proof
eqV1Sym x _ = absurd x

{-@ eqV1Trans :: x:_ -> y:_ -> z:_ -> { eqV1 x y && eqV1 y z ==> eqV1 x z } @-}
eqV1Trans :: V1 p -> V1 p -> V1 p -> Proof
eqV1Trans x _ _ = absurd x

{- veqV1 :: VerifiedEq (V1 p) @-}
veqV1 :: VerifiedEq (V1 p)
veqV1 = VerifiedEq eqV1 eqV1Refl eqV1Sym eqV1Trans

{-@ data U1 p = U1 @-}

{-@ reflect eqU1 @-}
eqU1 :: U1 p -> U1 p -> Bool
eqU1 _ _ = True

{-@ eqU1Refl :: x:_  -> { eqU1 x x } @-}
eqU1Refl :: U1 p -> Proof
eqU1Refl x = eqU1 x x *** QED

{-@ eqU1Sym :: x:_ -> y:_  -> { eqU1 x y ==> eqU1 y x } @-}
eqU1Sym :: U1 p -> U1 p -> Proof
eqU1Sym x y = eqU1 x y ==. eqU1 y x *** QED

{-@ eqU1Trans :: x:_ -> y:_  -> z:_  -> { eqU1 x y && eqU1 y z ==> eqU1 x z } @-}
eqU1Trans :: U1 p -> U1 p -> U1 p -> Proof
eqU1Trans x y z = (eqU1 x y && eqU1 y z) ==. eqU1 x z *** QED

{- veqU1 :: VerifiedEq (U1 p) @-}
veqU1 :: VerifiedEq (U1 p)
veqU1 = VerifiedEq eqU1 eqU1Refl eqU1Sym eqU1Trans

{- newtype Par1 p = Par1 { unPar1 :: p } @-}

{-@ reflect unPar1 @-}
unPar1 :: Par1 p -> p 
unPar1 (Par1 p) = p

{-@ reflect eqPar1 @-}
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

-- {-@ veqPar1 :: VerifiedEq p -> VerifiedEq (Par1 p) @-}
veqPar1 :: VerifiedEq p -> VerifiedEq (Par1 p)
veqPar1 (VerifiedEq eqP eqPRefl eqPSym eqPTrans)
  = VerifiedEq (eqPar1      eqP)
               (eqPar1Refl  eqP eqPRefl)
               (eqPar1Sym   eqP eqPSym)
               (eqPar1Trans eqP eqPTrans)

{-
{-@ newtype Rec1 f p = Rec1 { unRec1 :: f p } @-}

{-@ reflect eqRec1 @-}
eqRec1 :: (f p -> f p -> Bool) -> Rec1 f p -> Rec1 f p -> Bool
eqRec1 eqFp x y = eqFp (unRec1 x) (unRec1 y)

{-@ eqRec1Refl :: eqFp:(f p -> f p -> Bool) -> eqFpRefl:(x:f p -> { eqFp x x })
               -> x:Rec1 f p -> { eqRec1 eqFp x x } @-}
eqRec1Refl :: (f p -> f p -> Bool) -> (f p -> Proof) -> Rec1 f p -> Proof
eqRec1Refl eqFp eqFpRefl x
  =   eqRec1 eqFp x x
  ==. eqFp (unRec1 x) (unRec1 x)
  ==. True ? eqFpRefl (unRec1 x)
  *** QED

{-@ eqRec1Sym :: eqFp:(f p -> f p -> Bool) -> eqFpSym:(x:f p -> y:f p -> { eqFp x y ==> eqFp y x })
              -> x:Rec1 f p -> y:Rec1 f p -> { eqRec1 eqFp x y ==> eqRec1 eqFp y x } @-}
eqRec1Sym :: (f p -> f p -> Bool) -> (f p -> f p -> Proof)
          -> Rec1 f p -> Rec1 f p -> Proof
eqRec1Sym eqFp eqFpSym x y
  =   eqRec1 eqFp x y
  ==. eqFp (unRec1 x) (unRec1 y)
  ==. eqFp (unRec1 y) (unRec1 x) ? eqFpSym (unRec1 x) (unRec1 y)
  ==. eqRec1 eqFp y x
  *** QED

{-@ eqRec1Trans :: eqFp:(f p -> f p -> Bool) -> eqFpTrans:(x:f p -> y:f p -> z:f p -> { eqFp x y && eqFp y z ==> eqFp x z })
                -> x:Rec1 f p -> y:Rec1 f p -> z:Rec1 f p -> { eqRec1 eqFp x y && eqRec1 eqFp y z ==> eqRec1 eqFp x z } @-}
eqRec1Trans :: (f p -> f p -> Bool) -> (f p -> f p -> f p -> Proof)
            -> Rec1 f p -> Rec1 f p -> Rec1 f p -> Proof
eqRec1Trans eqFp eqFpTrans x y z
  =   (eqRec1 eqFp x y && eqRec1 eqFp y z)
  ==. (eqFp (unRec1 x) (unRec1 y) && eqFp (unRec1 y) (unRec1 z))
  ==. eqFp (unRec1 x) (unRec1 z) ? eqFpTrans (unRec1 x) (unRec1 y) (unRec1 z)
  ==. eqRec1 eqFp x z
  *** QED

{-@ veqRec1 :: VerifiedEq (f p) -> VerifiedEq (Rec1 f p) @-}
veqRec1 :: VerifiedEq (f p) -> VerifiedEq (Rec1 f p)
veqRec1 (VerifiedEq eqFp eqFpRefl eqFpSym eqFpTrans)
  = VerifiedEq (eqRec1      eqFp)
               (eqRec1Refl  eqFp eqFpRefl)
               (eqRec1Sym   eqFp eqFpSym)
               (eqRec1Trans eqFp eqFpTrans)

{-@ newtype K1 i c p = K1 { unK1 :: c } @-}

{-@ reflect eqK1 @-}
eqK1 :: (c -> c -> Bool) -> K1 i c p -> K1 i c p -> Bool
eqK1 eqC x y = eqC (unK1 x) (unK1 y)

{-@ eqK1Refl :: eqC:(c -> c -> Bool) -> eqCRefl:(x:c -> { eqC x x })
             -> x:K1 i c p -> { eqK1 eqC x x } @-}
eqK1Refl :: (c -> c -> Bool) -> (c -> Proof) -> K1 i c p -> Proof
eqK1Refl eqC eqCRefl x
  =   eqK1 eqC x x
  ==. eqC (unK1 x) (unK1 x)
  ==. True ? eqCRefl (unK1 x)
  *** QED

{-@ eqK1Sym :: eqC:(c -> c -> Bool) -> eqCSym:(x:c -> y:c -> { eqC x y ==> eqC y x })
            -> x:K1 i c p -> y:K1 i c p -> { eqK1 eqC x y ==> eqK1 eqC y x } @-}
eqK1Sym :: (c -> c -> Bool) -> (c -> c -> Proof)
        -> K1 i c p -> K1 i c p -> Proof
eqK1Sym eqC eqCSym x y
  =   eqK1 eqC x y
  ==. eqC (unK1 x) (unK1 y)
  ==. eqC (unK1 y) (unK1 x) ? eqCSym (unK1 x) (unK1 y)
  ==. eqK1 eqC y x
  *** QED

{-@ eqK1Trans :: eqC:(c -> c -> Bool) -> eqCTrans:(x:c -> y:c -> z:c -> { eqC x y && eqC y z ==> eqC x z })
              -> x:K1 i c p -> y:K1 i c p -> z:K1 i c p -> { eqK1 eqC x y && eqK1 eqC y z ==> eqK1 eqC x z } @-}
eqK1Trans :: (c -> c -> Bool) -> (c -> c -> c -> Proof)
          -> K1 i c p -> K1 i c p -> K1 i c p -> Proof
eqK1Trans eqC eqCTrans x y z
  =   (eqK1 eqC x y && eqK1 eqC y z)
  ==. (eqC (unK1 x) (unK1 y) && eqC (unK1 y) (unK1 z))
  ==. eqC (unK1 x) (unK1 z) ? eqCTrans (unK1 x) (unK1 y) (unK1 z)
  ==. eqK1 eqC x z
  *** QED

{-@ veqK1 :: VerifiedEq c -> VerifiedEq (K1 i c p) @-}
veqK1 :: VerifiedEq c -> VerifiedEq (K1 i c p)
veqK1 (VerifiedEq eqC eqCRefl eqCSym eqCTrans)
  = VerifiedEq (eqK1      eqC)
               (eqK1Refl  eqC eqCRefl)
               (eqK1Sym   eqC eqCSym)
               (eqK1Trans eqC eqCTrans)

{-@ newtype M1 i c f p = M1 { unM1 :: f p } @-}

{-@ reflect eqM1 @-}
eqM1 :: (f p -> f p -> Bool) -> M1 i c f p -> M1 i c f p -> Bool
eqM1 eqFp x y = eqFp (unM1 x) (unM1 y)

{-@ eqM1Refl :: eqFp:(f p -> f p -> Bool) -> eqFpRefl:(x:f p -> { eqFp x x })
             -> x:M1 i c f p -> { eqM1 eqFp x x } @-}
eqM1Refl :: (f p -> f p -> Bool) -> (f p -> Proof) -> M1 i c f p -> Proof
eqM1Refl eqFp eqFpRefl x
  =   eqM1 eqFp x x
  ==. eqFp (unM1 x) (unM1 x)
  ==. True ? eqFpRefl (unM1 x)
  *** QED

{-@ eqM1Sym :: eqFp:(f p -> f p -> Bool) -> eqFpSym:(x:f p -> y:f p -> { eqFp x y ==> eqFp y x })
            -> x:M1 i c f p -> y:M1 i c f p -> { eqM1 eqFp x y ==> eqM1 eqFp y x } @-}
eqM1Sym :: (f p -> f p -> Bool) -> (f p -> f p -> Proof)
        -> M1 i c f p -> M1 i c f p -> Proof
eqM1Sym eqFp eqFpSym x y
  =   eqM1 eqFp x y
  ==. eqFp (unM1 x) (unM1 y)
  ==. eqFp (unM1 y) (unM1 x) ? eqFpSym (unM1 x) (unM1 y)
  ==. eqM1 eqFp y x
  *** QED

{-@ eqM1Trans :: eqFp:(f p -> f p -> Bool) -> eqFpTrans:(x:f p -> y:f p -> z:f p -> { eqFp x y && eqFp y z ==> eqFp x z })
              -> x:M1 i c f p -> y:M1 i c f p -> z:M1 i c f p -> { eqM1 eqFp x y && eqM1 eqFp y z ==> eqM1 eqFp x z } @-}
eqM1Trans :: (f p -> f p -> Bool) -> (f p -> f p -> f p -> Proof)
          -> M1 i c f p -> M1 i c f p -> M1 i c f p -> Proof
eqM1Trans eqFp eqFpTrans x y z
  =   (eqM1 eqFp x y && eqM1 eqFp y z)
  ==. (eqFp (unM1 x) (unM1 y) && eqFp (unM1 y) (unM1 z))
  ==. eqFp (unM1 x) (unM1 z) ? eqFpTrans (unM1 x) (unM1 y) (unM1 z)
  ==. eqM1 eqFp x z
  *** QED

{-@ veqM1 :: VerifiedEq (f p) -> VerifiedEq (M1 i c f p) @-}
veqM1 :: VerifiedEq (f p) -> VerifiedEq (M1 i c f p)
veqM1 (VerifiedEq eqFp eqFpRefl eqFpSym eqFpTrans)
  = VerifiedEq (eqM1      eqFp)
               (eqM1Refl  eqFp eqFpRefl)
               (eqM1Sym   eqFp eqFpSym)
               (eqM1Trans eqFp eqFpTrans)

{-
{-@ data (:+:) f g p = L1 (f p) | R1 (g p) @-}

{-@ reflect eqSum @-}
eqSum :: (f p -> f p -> Bool) -> (g p -> g p -> Bool)
      -> (:+:) f g p -> (:+:) f g p -> Bool
eqSum eqFp _    (L1 x) (L1 y) = eqFp x y
eqSum _    eqGp (R1 x) (R1 y) = eqGp x y
eqSum _    _    (L1 _) (R1 _) = False
eqSum _    _    (R1 _) (L1 _) = False
-}
-}
