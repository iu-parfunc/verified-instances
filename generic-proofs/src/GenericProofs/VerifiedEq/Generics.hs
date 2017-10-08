{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exactdc"        @-}
{-@ LIQUID "--noadt"          @-}
{-# LANGUAGE EmptyCase     #-}
{-# LANGUAGE TypeOperators #-}
module GenericProofs.VerifiedEq.Generics where

import Language.Haskell.Liquid.ProofCombinators
import GenericProofs.VerifiedEq

import Generics.Deriving.Newtypeless.Base.Internal

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

{-@ axiomatize eqK1 @-}
eqK1 :: (c -> c -> Bool) -> K1 i c p -> K1 i c p -> Bool
eqK1 eqC (K1 a) (K1 b) = eqC a b

{-@ eqK1Refl :: eqC:(c -> c -> Bool) -> eqCRefl:(x:c -> { eqC x x })
             -> x:K1 i c p -> { eqK1 eqC x x } @-}
eqK1Refl :: (c -> c -> Bool) -> (c -> Proof) -> K1 i c p -> Proof
eqK1Refl eqC eqCRefl x@(K1 a)
  =   eqK1 eqC x x
  ==. eqC a a
  ==. True ? eqCRefl a
  *** QED

{-@ eqK1Sym :: eqC:(c -> c -> Bool) -> eqCSym:(x:c -> y:c -> { eqC x y ==> eqC y x })
            -> x:K1 i c p -> y:K1 i c p -> { eqK1 eqC x y ==> eqK1 eqC y x } @-}
eqK1Sym :: (c -> c -> Bool) -> (c -> c -> Proof)
        -> K1 i c p -> K1 i c p -> Proof
eqK1Sym eqC eqCSym x@(K1 a) y@(K1 b)
  =   eqK1 eqC x y
  ==. eqC a b
  ==. eqC b a ? eqCSym a b
  ==. eqK1 eqC y x
  *** QED

{-@ eqK1Trans :: eqC:(c -> c -> Bool) -> eqCTrans:(x:c -> y:c -> z:c -> { eqC x y && eqC y z ==> eqC x z })
              -> x:K1 i c p -> y:K1 i c p -> z:K1 i c p -> { eqK1 eqC x y && eqK1 eqC y z ==> eqK1 eqC x z } @-}
eqK1Trans :: (c -> c -> Bool) -> (c -> c -> c -> Proof)
          -> K1 i c p -> K1 i c p -> K1 i c p -> Proof
eqK1Trans eqC eqCTrans x@(K1 a) y@(K1 b) z@(K1 c)
  =   (eqK1 eqC x y && eqK1 eqC y z)
  ==. (eqC a b && eqC b c)
  ==. eqC a c ? eqCTrans a b c
  ==. eqK1 eqC x z
  *** QED

veqK1 :: VerifiedEq c -> VerifiedEq (K1 i c p)
veqK1 (VerifiedEq eqC eqCRefl eqCSym eqCTrans)
  = VerifiedEq (eqK1      eqC)
               (eqK1Refl  eqC eqCRefl)
               (eqK1Sym   eqC eqCSym)
               (eqK1Trans eqC eqCTrans)

{-@ axiomatize eqM1 @-}
eqM1 :: (f p -> f p -> Bool) -> M1 i c f p -> M1 i c f p -> Bool
eqM1 eqFp (M1 a) (M1 b) = eqFp a b

{-@ eqM1Refl :: eqFp:(f p -> f p -> Bool) -> eqFpRefl:(x:f p -> { eqFp x x })
             -> x:M1 i c f p -> { eqM1 eqFp x x } @-}
eqM1Refl :: (f p -> f p -> Bool) -> (f p -> Proof) -> M1 i c f p -> Proof
eqM1Refl eqFp eqFpRefl x@(M1 a)
  =   eqM1 eqFp x x
  ==. eqFp a a
  ==. True ? eqFpRefl a
  *** QED

{-@ eqM1Sym :: eqFp:(f p -> f p -> Bool) -> eqFpSym:(x:f p -> y:f p -> { eqFp x y ==> eqFp y x })
            -> x:M1 i c f p -> y:M1 i c f p -> { eqM1 eqFp x y ==> eqM1 eqFp y x } @-}
eqM1Sym :: (f p -> f p -> Bool) -> (f p -> f p -> Proof)
        -> M1 i c f p -> M1 i c f p -> Proof
eqM1Sym eqFp eqFpSym x@(M1 a) y@(M1 b)
  =   eqM1 eqFp x y
  ==. eqFp a b
  ==. eqFp b a ? eqFpSym a b
  ==. eqM1 eqFp y x
  *** QED

{-@ eqM1Trans :: eqFp:(f p -> f p -> Bool) -> eqFpTrans:(x:f p -> y:f p -> z:f p -> { eqFp x y && eqFp y z ==> eqFp x z })
              -> x:M1 i c f p -> y:M1 i c f p -> z:M1 i c f p -> { eqM1 eqFp x y && eqM1 eqFp y z ==> eqM1 eqFp x z } @-}
eqM1Trans :: (f p -> f p -> Bool) -> (f p -> f p -> f p -> Proof)
          -> M1 i c f p -> M1 i c f p -> M1 i c f p -> Proof
eqM1Trans eqFp eqFpTrans x@(M1 a) y@(M1 b) z@(M1 c)
  =   (eqM1 eqFp x y && eqM1 eqFp y z)
  ==. (eqFp a b && eqFp b c)
  ==. eqFp a c ? eqFpTrans a b c
  ==. eqM1 eqFp x z
  *** QED

veqM1 :: VerifiedEq (f p) -> VerifiedEq (M1 i c f p)
veqM1 (VerifiedEq eqFp eqFpRefl eqFpSym eqFpTrans)
  = VerifiedEq (eqM1      eqFp)
               (eqM1Refl  eqFp eqFpRefl)
               (eqM1Sym   eqFp eqFpSym)
               (eqM1Trans eqFp eqFpTrans)

{-@ axiomatize eqSum @-}
eqSum :: (f p -> f p -> Bool) -> (g p -> g p -> Bool)
      -> Sum f g p -> Sum f g p -> Bool
eqSum eqFp _    (L1 x) (L1 y) = eqFp x y
eqSum _    eqGp (R1 x) (R1 y) = eqGp x y
eqSum _    _    (L1 _) (R1 _) = False
eqSum _    _    (R1 _) (L1 _) = False

{-@ eqSumRefl :: eqFp:(f p -> f p -> Bool) -> eqFpRefl:(x:f p -> { eqFp x x })
              -> eqGp:(g p -> g p -> Bool) -> eqGpRefl:(y:g p -> { eqGp y y })
              -> p:Sum f g p
              -> { eqSum eqFp eqGp p p }
@-}
eqSumRefl :: (f p -> f p -> Bool) -> (f p -> Proof)
          -> (g p -> g p -> Bool) -> (g p -> Proof)
          -> Sum f g p -> Proof
eqSumRefl eqFp eqFpRefl eqGp _ p@(L1 x) =
      eqSum eqFp eqGp p p
  ==. eqFp x x
  ==. True ? eqFpRefl x
  *** QED
eqSumRefl eqFp _ eqGp eqGpRefl p@(R1 y) =
      eqSum eqFp eqGp p p
  ==. eqGp y y
  ==. True ? eqGpRefl y
  *** QED

{-@ eqSumSym :: eqFp:(f p -> f p -> Bool)
             -> eqFpSym:(x:f p -> y:f p -> { eqFp x y ==> eqFp y x })
             -> eqGp:(g p -> g p -> Bool)
             -> eqGpSym:(x:g p -> y:g p -> { eqGp x y ==> eqGp y x })
             -> p:Sum f g p -> q:Sum f g p
             -> { eqSum eqFp eqGp p q ==> eqSum eqFp eqGp q p }
@-}
eqSumSym :: (f p -> f p -> Bool) -> (f p -> f p -> Proof)
         -> (g p -> g p -> Bool) -> (g p -> g p -> Proof)
         -> Sum f g p -> Sum f g p -> Proof
eqSumSym eqFp eqFpSym eqGp _ p@(L1 x) q@(L1 y) =
      eqSum eqFp eqGp p q
  ==. eqFp x y
  ==. eqFp y x ? eqFpSym x y
  ==. eqSum eqFp eqGp q p
  *** QED
eqSumSym eqFp _ eqGp _ p@(L1 _) q@(R1 _) =
      eqSum eqFp eqGp p q
  ==. False
  *** QED
eqSumSym eqFp _ eqGp _ p@(R1 _) q@(L1 _) =
      eqSum eqFp eqGp p q
  ==. False
  *** QED
eqSumSym eqFp _ eqGp eqGpSym p@(R1 x) q@(R1 y) =
      eqSum eqFp eqGp p q
  ==. eqGp x y
  ==. eqGp y x ? eqGpSym x y
  ==. eqSum eqFp eqGp q p
  *** QED

{-@ eqSumTrans :: eqFp:(f p -> f p -> Bool)
               -> eqFpTrans:(x:f p -> y:f p -> z:f p -> { eqFp x y && eqFp y z ==> eqFp x z })
               -> eqGp:(g p -> g p -> Bool)
               -> eqGpTrans:(x:g p -> y:g p -> z:g p -> { eqGp x y && eqGp y z ==> eqGp x z })
               -> p:Sum f g p -> q:Sum f g p -> r:Sum f g p
               -> { eqSum eqFp eqGp p q && eqSum eqFp eqGp q r ==> eqSum eqFp eqGp p r }
@-}
eqSumTrans :: (f p -> f p -> Bool) -> (f p -> f p -> f p -> Proof)
           -> (g p -> g p -> Bool) -> (g p -> g p -> g p -> Proof)
           -> Sum f g p -> Sum f g p -> Sum f g p -> Proof
eqSumTrans eqFp eqFpTrans eqGp _ p@(L1 x) q@(L1 y) r@(L1 z) =
      (eqSum eqFp eqGp p q && eqSum eqFp eqGp q r)
  ==. (eqFp x y && eqFp y z)
  ==. eqFp x z ? eqFpTrans x y z
  ==. eqSum eqFp eqGp p r
  *** QED
eqSumTrans eqFp _ eqGp _ p@(L1 x) q@(L1 y) r@(R1 _) =
      (eqSum eqFp eqGp p q && eqSum eqFp eqGp q r)
  ==. (eqFp x y && False)
  ==. False
  *** QED
eqSumTrans eqFp _ eqGp _ p@(L1 _) q@(R1 _) r@(L1 _) =
      (eqSum eqFp eqGp p q && eqSum eqFp eqGp q r)
  ==. (False && False)
  ==. False
  *** QED
eqSumTrans eqFp _ eqGp _ p@(L1 _) q@(R1 y) r@(R1 z) =
      (eqSum eqFp eqGp p q && eqSum eqFp eqGp q r)
  ==. (False && eqGp y z)
  ==. False
  *** QED
eqSumTrans eqFp _ eqGp _ p@(R1 _) q@(L1 y) r@(L1 z) =
      (eqSum eqFp eqGp p q && eqSum eqFp eqGp q r)
  ==. (False && eqFp y z)
  ==. False
  *** QED
eqSumTrans eqFp _ eqGp _ p@(R1 _) q@(L1 _) r@(R1 _) =
      (eqSum eqFp eqGp p q && eqSum eqFp eqGp q r)
  ==. (False && False)
  ==. False
  *** QED
eqSumTrans eqFp _ eqGp _ p@(R1 x) q@(R1 y) r@(L1 _) =
      (eqSum eqFp eqGp p q && eqSum eqFp eqGp q r)
  ==. (eqGp x y && False)
  ==. False
  *** QED
eqSumTrans eqFp _ eqGp eqGpTrans p@(R1 x) q@(R1 y) r@(R1 z) =
      (eqSum eqFp eqGp p q && eqSum eqFp eqGp q r)
  ==. (eqGp x y && eqGp y z)
  ==. eqGp x z ? eqGpTrans x y z
  ==. eqSum eqFp eqGp p r
  *** QED

veqSum :: VerifiedEq (f p) -> VerifiedEq (g p) -> VerifiedEq (Sum f g p)
veqSum (VerifiedEq eqFp eqFpRefl eqFpSym eqFpTrans) (VerifiedEq eqGp eqGpRefl eqGpSym eqGpTrans) =
  VerifiedEq (eqSum eqFp eqGp)
             (eqSumRefl eqFp eqFpRefl eqGp eqGpRefl)
             (eqSumSym eqFp eqFpSym eqGp eqGpSym)
             (eqSumTrans eqFp eqFpTrans eqGp eqGpTrans)

{-@ axiomatize eqProd @-}
eqProd :: (f p -> f p -> Bool) -> (g p -> g p -> Bool)
       -> Product f g p -> Product f g p -> Bool
eqProd eqFp eqGp (Product p1 p2) (Product q1 q2) = eqFp p1 q1 && eqGp p2 q2

{-@ eqProdRefl :: eqFp:(f p -> f p -> Bool) -> eqFpRefl:(x:f p -> { eqFp x x })
               -> eqGp:(g p -> g p -> Bool) -> eqGpRefl:(y:g p -> { eqGp y y })
               -> p:Product f g p
               -> { eqProd eqFp eqGp p p }
@-}
eqProdRefl :: (f p -> f p -> Bool) -> (f p -> Proof)
           -> (g p -> g p -> Bool) -> (g p -> Proof)
           -> Product f g p -> Proof
eqProdRefl eqFp eqFpRefl eqGp eqGpRefl p@(Product x y) =
      eqProd eqFp eqGp p p
  ==. (eqFp x x && eqGp y y)
  ==. (True && eqGp y y) ? eqFpRefl x
  ==. (True && True)     ? eqGpRefl y
  ==. True
  *** QED

{-@ eqProdSym :: eqFp:(f p -> f p -> Bool)
              -> eqFpSym:(x:f p -> y:f p -> { eqFp x y ==> eqFp y x })
              -> eqGp:(g p -> g p -> Bool)
              -> eqGpSym:(x:g p -> y:g p -> { eqGp x y ==> eqGp y x })
              -> p:Product f g p -> q:Product f g p
              -> { eqProd eqFp eqGp p q ==> eqProd eqFp eqGp q p }
@-}
eqProdSym :: (f p -> f p -> Bool) -> (f p -> f p -> Proof)
          -> (g p -> g p -> Bool) -> (g p -> g p -> Proof)
          -> Product f g p -> Product f g p -> Proof
eqProdSym eqFp eqFpSym eqGp eqGpSym p@(Product x1 y1) q@(Product x2 y2) =
      eqProd eqFp eqGp p q
  ==. (eqFp x1 x2 && eqGp y1 y2)
  ==. (eqFp x2 x1 && eqGp y1 y2) ? eqFpSym x1 x2
  ==. (eqFp x2 x1 && eqGp y2 y1) ? eqGpSym y1 y2
  ==. (eqProd eqFp eqGp (Product x2 y2) (Product x1 y1))
  ==. eqProd eqFp eqGp q p
  *** QED

{-@ eqProdTrans :: eqFp:(f p -> f p -> Bool)
                 -> eqFpTrans:(x:f p -> y:f p -> z:f p -> { eqFp x y && eqFp y z ==> eqFp x z })
                -> eqGp:(g p -> g p -> Bool)
                -> eqGpTrans:(x:g p -> y:g p -> z:g p -> { eqGp x y && eqGp y z ==> eqGp x z })
                -> p:Product f g p -> q:Product f g p -> r:Product f g p
                -> { eqProd eqFp eqGp p q && eqProd eqFp eqGp q r ==> eqProd eqFp eqGp p r }
@-}
eqProdTrans :: (f p -> f p -> Bool) -> (f p -> f p -> f p -> Proof)
            -> (g p -> g p -> Bool) -> (g p -> g p -> g p -> Proof)
            -> Product f g p -> Product f g p -> Product f g p -> Proof
eqProdTrans eqFp eqFpTrans eqGp eqGpTrans p@(Product x1 y1) q@(Product x2 y2) r@(Product x3 y3) =
      (eqProd eqFp eqGp p q && eqProd eqFp eqGp q r)
  ==. ((eqFp x1 x2 && eqGp y1 y2) && (eqFp x2 x3 && eqGp y2 y3))
  ==. ((eqFp x1 x2 && eqFp x2 x3) && (eqGp y1 y2 && eqGp y2 y3))
  ==. (eqFp x1 x3 && (eqGp y1 y2 && eqGp y2 y3)) ? eqFpTrans x1 x2 x3
  ==. (eqFp x1 x3 && eqGp y1 y3)                ? eqGpTrans y1 y2 y3
  ==. eqProd eqFp eqGp p r
  *** QED

veqProd :: VerifiedEq (f p) -> VerifiedEq (g p) -> VerifiedEq (Product f g p)
veqProd (VerifiedEq eqFp eqFpRefl eqFpSym eqFpTrans) (VerifiedEq eqGp eqGpRefl eqGpSym eqGpTrans) =
  VerifiedEq (eqProd eqFp eqGp)
             (eqProdRefl eqFp eqFpRefl eqGp eqGpRefl)
             (eqProdSym eqFp eqFpSym eqGp eqGpSym)
             (eqProdTrans eqFp eqFpTrans eqGp eqGpTrans)
