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

{-@ leqK1Antisym :: leqC:(c -> c -> Bool)
                 -> leqCAntisym:(x:c -> y:c -> { leqC x y && leqC y x ==> x == y })
                 -> x:K1 i c p -> y:K1 i c p
                 -> { leqK1 leqC x y && leqK1 leqC y x ==> x == y }
@-}
leqK1Antisym :: Eq c
             => (c -> c -> Bool)
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

vordK1 :: Eq c => VerifiedOrd c -> VerifiedOrd (K1 i c p)
vordK1 (VerifiedOrd leqC leqCRefl leqCAntisym leqCTrans leqCTotal)
  = VerifiedOrd (leqK1 leqC)
                (leqK1Refl leqC leqCRefl)
                (leqK1Antisym leqC leqCAntisym)
                (leqK1Trans leqC leqCTrans)
                (leqK1Total leqC leqCTotal)

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

{-@ leqM1Antisym :: leqFP:(f p -> f p -> Bool)
                 -> leqFPAntisym:(x:(f p) -> y:(f p) -> { leqFP x y && leqFP y x ==> x == y })
                 -> x:M1 i c f p
                 -> y:M1 i c f p
                 -> { leqM1 leqFP x y && leqM1 leqFP y x ==> x == y }
@-}
leqM1Antisym :: Eq (f p)
             => (f p -> f p -> Bool)
             -> (f p -> f p -> Proof)
             -> M1 i c f p
             -> M1 i c f p
             -> Proof
leqM1Antisym leqFP leqFPAntisym x@(M1 m1) y@(M1 m2)
  =   (leqM1 leqFP x y && leqM1 leqFP y x)
  ==. (leqFP m1 m2 && leqFP m2 m1)
  ==. m1 == m2 ? leqFPAntisym m1 m2
  ==. x == y
  *** QED

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

{-@ leqM1Total :: leqFP:(f p -> f p -> Bool)
               -> leqFPTotal:(x:(f p) -> y:(f p) -> { leqFP x y || leqFP y x })
               -> x:M1 i c f p -> y:M1 i c f p
               -> { leqM1 leqFP x y || leqM1 leqFP y x } @-}
leqM1Total :: (f p -> f p -> Bool)
           -> (f p -> f p -> Proof)
           -> M1 i c f p -> M1 i c f p -> Proof
leqM1Total leqFP leqFPTotal x@(M1 m1) y@(M1 m2)
  =   (leqM1 leqFP x y || leqM1 leqFP y x)
  ==. (leqFP m1 m2 || leqFP m2 m1)
  ==. True ? leqFPTotal m1 m2
  *** QED

vordM1 :: Eq (f p) => VerifiedOrd (f p) -> VerifiedOrd (M1 i c f p)
vordM1 (VerifiedOrd leqFP leqFPRefl leqFPAntisym leqFPTrans leqFPTotal) =
    VerifiedOrd
        (leqM1 leqFP)
        (leqM1Refl leqFP leqFPRefl)
        (leqM1Antisym leqFP leqFPAntisym)
        (leqM1Trans leqFP leqFPTrans)
        (leqM1Total leqFP leqFPTotal)

{-@ axiomatize leqSum @-}
leqSum :: (f p -> f p -> Bool) -> (g p -> g p -> Bool)
       -> Sum f g p -> Sum f g p -> Bool
leqSum leqFP leqGP (L1 x) (L1 y) = leqFP x y
leqSum leqFP leqGP (L1 x) (R1 y) = True
leqSum leqFP leqGP (R1 x) (L1 y) = False
leqSum leqFP leqGP (R1 x) (R1 y) = leqGP x y
{-# INLINE leqSum #-}

{-@ leqSumRefl :: leqFP:(f p -> f p -> Bool) -> leqFPRefl:(x:f p -> { leqFP x x })
               -> leqGP:(g p -> g p -> Bool) -> leqGPRefl:(y:g p -> { leqGP y y })
               -> p:Sum f g p
               -> { leqSum leqFP leqGP p p }
@-}
leqSumRefl :: (f p -> f p -> Bool) -> (f p -> Proof)
           -> (g p -> g p -> Bool) -> (g p -> Proof)
           -> Sum f g p -> Proof
leqSumRefl leqFP leqFPRefl leqGP leqGPRefl p@(L1 x) =
      leqSum leqFP leqGP p p
  ==. leqFP x x
  ==. True ? leqFPRefl x
  *** QED
leqSumRefl leqFP leqFPRefl leqGP leqGPRefl p@(R1 y) =
      leqSum leqFP leqGP p p
  ==. leqGP y y
  ==. True ? leqGPRefl y
  *** QED

{-@ leqSumAntisym :: leqFP:(f p -> f p -> Bool) -> leqFPAntisym:(x:f p -> y:f p -> { leqFP x y && leqFP y x ==> x == y })
                  -> leqGP:(g p -> g p -> Bool) -> leqGPAntisym:(x:g p -> y:g p -> { leqGP x y && leqGP y x ==> x == y })
                  -> p:Sum f g p -> q:Sum f g p
                  -> { leqSum leqFP leqGP p q && leqSum leqFP leqGP q p ==> p == q }
@-}
leqSumAntisym :: (Eq (f p), Eq (g p))
              => (f p -> f p -> Bool) -> (f p -> f p -> Proof)
              -> (g p -> g p -> Bool) -> (g p -> g p -> Proof)
              -> Sum f g p -> Sum f g p -> Proof
leqSumAntisym leqFP leqFPAntisym leqGP leqGPAntisym p@(L1 x) q@(L1 y)
  =   (leqSum leqFP leqGP p q && leqSum leqFP leqGP q p)
  ==. (leqFP x y && leqFP y x)
  ==. x == y ? leqFPAntisym x y
  *** QED
leqSumAntisym leqFP leqFPAntisym leqGP leqGPAntisym p@(L1 x) q@(R1 y)
  =   (leqSum leqFP leqGP p q && leqSum leqFP leqGP q p)
  ==. (True && False)
  ==. False
  ==. p == q
  *** QED
leqSumAntisym leqFP leqFPAntisym leqGP leqGPAntisym p@(R1 x) q@(L1 y)
  =   (leqSum leqFP leqGP p q && leqSum leqFP leqGP q p)
  ==. (False && True)
  ==. False
  ==. p == q
  *** QED
leqSumAntisym leqFP leqFPAntisym leqGP leqGPAntisym p@(R1 x) q@(R1 y)
  =   (leqSum leqFP leqGP p q && leqSum leqFP leqGP q p)
  ==. (leqGP x y && leqGP y x)
  ==. x == y ? leqGPAntisym x y
  *** QED

{-@ leqSumTrans :: leqFP:(f p -> f p -> Bool)
                -> leqFPTrans:(x:f p -> y:f p -> z:f p -> { leqFP x y && leqFP y z ==> leqFP x z })
                -> leqGP:(g p -> g p -> Bool)
                -> leqGPTrans:(x:g p -> y:g p -> z:g p -> { leqGP x y && leqGP y z ==> leqGP x z })
                -> p:Sum f g p -> q:Sum f g p -> r:Sum f g p
                -> { leqSum leqFP leqGP p q && leqSum leqFP leqGP q r ==> leqSum leqFP leqGP p r }
@-}
leqSumTrans :: (f p -> f p -> Bool) -> (f p -> f p -> f p -> Proof)
            -> (g p -> g p -> Bool) -> (g p -> g p -> g p -> Proof)
            -> Sum f g p -> Sum f g p -> Sum f g p -> Proof
leqSumTrans leqFP leqFPTrans leqGP leqGPTrans p@(L1 x) q@(L1 y) r@(L1 z) =
      (leqSum leqFP leqGP p q && leqSum leqFP leqGP q r)
  ==. (leqFP x y && leqFP y z)
  ==. leqFP x z ? leqFPTrans x y z
  ==. leqSum leqFP leqGP p r
  *** QED
leqSumTrans leqFP leqFPTrans leqGP leqGPTrans p@(L1 x) q@(L1 y) r@(R1 z) =
      (leqSum leqFP leqGP p q && leqSum leqFP leqGP q r)
  ==. (leqFP x y && True)
  ==. leqSum leqFP leqGP p r
  *** QED
leqSumTrans leqFP leqFPTrans leqGP leqGPTrans p@(L1 x) q@(R1 y) r@(L1 z) =
      (leqSum leqFP leqGP p q && leqSum leqFP leqGP q r)
  ==. (True && False)
  ==. leqSum leqFP leqGP p r
  *** QED
leqSumTrans leqFP leqFPTrans leqGP leqGPTrans p@(L1 x) q@(R1 y) r@(R1 z) =
      (leqSum leqFP leqGP p q && leqSum leqFP leqGP q r)
  ==. (True && leqGP y z)
  ==. leqSum leqFP leqGP p r
  *** QED
leqSumTrans leqFP leqFPTrans leqGP leqGPTrans p@(R1 x) q@(L1 y) r@(L1 z) =
      (leqSum leqFP leqGP p q && leqSum leqFP leqGP q r)
  ==. (False && leqFP y z)
  ==. leqSum leqFP leqGP p r
  *** QED
leqSumTrans leqFP leqFPTrans leqGP leqGPTrans p@(R1 x) q@(L1 y) r@(R1 z) =
      (leqSum leqFP leqGP p q && leqSum leqFP leqGP q r)
  ==. (False && True)
  ==. leqSum leqFP leqGP p r
  *** QED
leqSumTrans leqFP leqFPTrans leqGP leqGPTrans p@(R1 x) q@(R1 y) r@(L1 z) =
      (leqSum leqFP leqGP p q && leqSum leqFP leqGP q r)
  ==. (leqGP x y && False)
  ==. leqSum leqFP leqGP p r
  *** QED
leqSumTrans leqFP leqFPTrans leqGP leqGPTrans p@(R1 x) q@(R1 y) r@(R1 z) =
      (leqSum leqFP leqGP p q && leqSum leqFP leqGP q r)
  ==. (leqGP x y && leqGP y z)
  ==. leqGP x z ? leqGPTrans x y z
  ==. leqSum leqFP leqGP p r
  *** QED

{-@ leqSumTotal :: leqFP:(f p -> f p -> Bool) -> leqFPTotal:(x:f p -> y:f p -> { leqFP x y || leqFP y x })
                -> leqGP:(g p -> g p -> Bool) -> leqGPTotal:(x:g p -> y:g p -> { leqGP x y || leqGP y x })
                -> p:Sum f g p -> q:Sum f g p
                -> { leqSum leqFP leqGP p q || leqSum leqFP leqGP q p }
@-}
leqSumTotal :: (f p -> f p -> Bool) -> (f p -> f p -> Proof)
            -> (g p -> g p -> Bool) -> (g p -> g p -> Proof)
            -> Sum f g p -> Sum f g p -> Proof
leqSumTotal leqFP leqFPTotal leqGP leqGPTotal p@(L1 x) q@(L1 y) =
      (leqSum leqFP leqGP p q || leqSum leqFP leqGP q p)
  ==. (leqFP x y || leqFP y x)
  ==. True ? leqFPTotal x y
  *** QED
leqSumTotal leqFP leqFPTotal leqGP leqGPTotal p@(L1 x) q@(R1 y) =
      (leqSum leqFP leqGP p q || leqSum leqFP leqGP q p)
  ==. (True || True)
  *** QED
leqSumTotal leqFP leqFPTotal leqGP leqGPTotal p@(R1 x) q@(L1 y) =
      (leqSum leqFP leqGP p q || leqSum leqFP leqGP q p)
  ==. (False || False)
  *** QED
leqSumTotal leqFP leqFPTotal leqGP leqGPTotal p@(R1 x) q@(R1 y) =
      (leqSum leqFP leqGP p q || leqSum leqFP leqGP q p)
  ==. (leqGP x y || leqGP y x)
  ==. True ? leqGPTotal x y
  *** QED

vordSum :: (Eq (f p), Eq (g p)) => VerifiedOrd (f p) -> VerifiedOrd (g p) -> VerifiedOrd (Sum f g p)
vordSum (VerifiedOrd leqFP leqFPRefl leqFPAntisym leqFPTrans leqFPTotal) (VerifiedOrd leqGP leqGPRefl leqGPAntisym leqGPTrans leqGPTotal) =
    VerifiedOrd
        (leqSum leqFP leqGP)
        (leqSumRefl leqFP leqFPRefl leqGP leqGPRefl)
        (leqSumAntisym leqFP leqFPAntisym leqGP leqGPAntisym)
        (leqSumTrans leqFP leqFPTrans leqGP leqGPTrans)
        (leqSumTotal leqFP leqFPTotal leqGP leqGPTotal)

{-@ axiomatize leqProd @-}
leqProd :: Eq (f p)
        => (f p -> f p -> Bool) -> (g p -> g p -> Bool)
        -> Product f g p -> Product f g p -> Bool
leqProd leqFP leqGP (Product x1 y1) (Product x2 y2) =
  if x1 == x2
    then leqGP y1 y2
    else leqFP x1 x2
{-# INLINE leqProd #-}

{-@ leqProdRefl :: leqFP:(f p -> f p -> Bool) -> leqFPRefl:(x:f p -> { leqFP x x })
                -> leqGP:(g p -> g p -> Bool) -> leqGPRefl:(y:g p -> { leqGP y y })
                -> p:Product f g p -> { leqProd leqFP leqGP p p }
@-}
leqProdRefl :: Eq (f p)
            => (f p -> f p -> Bool) -> (f p -> Proof)
            -> (g p -> g p -> Bool) -> (g p -> Proof)
            -> Product f g p -> Proof
leqProdRefl leqFP leqFPRefl leqGP leqGPRefl p@(Product x y) =
      leqProd leqFP leqGP p p
  ==. (if x == x then leqGP y y else leqFP x x)
  ==. leqGP y y
  ==. True ? leqGPRefl y
  *** QED

{-@ leqProdAntisym :: leqFP:(f p -> f p -> Bool)
                   -> leqFPAntisym:(x:f p -> y:f p -> { leqFP x y && leqFP y x ==> x == y })
                   -> leqGP:(g p -> g p -> Bool)
                   -> leqGPAntisym:(x:g p -> y:g p -> { leqGP x y && leqGP y x ==> x == y })
                   -> p:Product f g p -> q:Product f g p
                   -> { leqProd leqFP leqGP p q && leqProd leqFP leqGP q p ==> p == q }
@-}
leqProdAntisym :: (Eq (f p), Eq (g p))
               => (f p -> f p -> Bool) -> (f p -> f p -> Proof)
               -> (g p -> g p -> Bool) -> (g p -> g p -> Proof)
               -> Product f g p -> Product f g p -> Proof
leqProdAntisym leqFP leqFPAntisym leqGP leqGPAntisym p@(Product x1 y1) q@(Product x2 y2) =
      (leqProd leqFP leqGP p q && leqProd leqFP leqGP q p)
  ==. ((if x1 == x2 then leqGP y1 y2 else leqFP x1 x2) && (if x2 == x1 then leqGP y2 y1 else leqFP x2 x1))
  ==. (if x1 == x2 then leqGP y1 y2 && leqGP y2 y1 else leqFP x1 x2 && leqFP x2 x1)
  ==. (if x1 == x2 then y1 == y2 else leqFP x1 x2 && leqFP x2 x1) ? leqGPAntisym y1 y2
  ==. (if x1 == x2 then y1 == y2 else x1 == x2)                 ? leqFPAntisym x1 x2
  ==. (x1 == x2 && y1 == y2)
  ==. (p == q)
  *** QED

{-@ leqProdTrans :: leqFP:(f p -> f p -> Bool)
                 -> leqFPAntisym:(x:f p -> y:f p -> { leqFP x y && leqFP y x ==> x == y })
                 -> leqFPTrans:(x:f p -> y:f p -> z:f p -> { leqFP x y && leqFP y z ==> leqFP x z })
                 -> leqGP:(g p -> g p -> Bool)
                 -> leqGPTrans:(x:g p -> y:g p -> z:g p -> { leqGP x y && leqGP y z ==> leqGP x z })
                 -> p:Product f g p -> q:Product f g p -> r:Product f g p
                 -> { leqProd leqFP leqGP p q && leqProd leqFP leqGP q r ==> leqProd leqFP leqGP p r }
@-}
leqProdTrans :: Eq (f p)
             => (f p -> f p -> Bool) -> (f p -> f p -> Proof) -> (f p -> f p -> f p -> Proof)
             -> (g p -> g p -> Bool) -> (g p -> g p -> g p -> Proof)
             -> Product f g p -> Product f g p -> Product f g p -> Proof
leqProdTrans leqFP leqFPAntisym leqFPTrans leqGP leqGPTrans p@(Product x1 y1) q@(Product x2 y2) r@(Product x3 y3) =
    case x1 == x2 of
      True  -> case x2 == x3 of
        True  ->  (leqProd leqFP leqGP p q && leqProd leqFP leqGP q r)
              ==. (leqGP y1 y2 && leqGP y2 y3)
              ==. leqGP y1 y3 ? leqGPTrans y1 y2 y3
              ==. (if x1 == x3 then leqGP y1 y3 else leqFP x1 x3)
              ==. leqProd leqFP leqGP p r
              *** QED
        False ->  (leqProd leqFP leqGP p q && leqProd leqFP leqGP q r)
              ==. (leqGP y1 y2 && leqFP x2 x3)
              ==. leqFP x1 x3
              ==. (if x1 == x3 then leqGP y1 y3 else leqFP x1 x3)
              ==. leqProd leqFP leqGP p r
              *** QED
      False -> case x2 == x3 of
        True  ->  (leqProd leqFP leqGP p q && leqProd leqFP leqGP q r)
              ==. (leqFP x1 x2 && leqGP y2 y3)
              ==. leqFP x1 x3
              ==. (if x1 == x3 then leqGP y1 y3 else leqFP x1 x3)
              ==. leqProd leqFP leqGP p r
              *** QED
        False -> case x1 == x3 of
          True  ->  (leqProd leqFP leqGP p q && leqProd leqFP leqGP q r)
                ==. (leqFP x1 x2 && leqFP x2 x3)
                ==. (leqFP x1 x2 && leqFP x2 x1)
                ==. (x1 == x2) ? leqFPAntisym x1 x2
                ==. leqGP y1 y3
                ==. (if x1 == x3 then leqGP y1 y3 else leqFP x1 x3)
                *** QED
          False ->  (leqProd leqFP leqGP p q && leqProd leqFP leqGP q r)
                ==. (leqFP x1 x2 && leqFP x2 x3)
                ==. leqFP x1 x3 ? leqFPTrans x1 x2 x3
                ==. (if x1 == x3 then leqGP y1 y3 else leqFP x1 x3)
                ==. leqProd leqFP leqGP p r
                *** QED

{-@ leqProdTotal :: leqFP:(f p -> f p -> Bool) -> leqFPTotal:(x:f p -> y:f p -> { leqFP x y || leqFP y x })
                 -> leqGP:(g p -> g p -> Bool) -> leqGPTotal:(x:g p -> y:g p -> { leqGP x y || leqGP y x })
                 -> p:Product f g p -> q:Product f g p
                 -> { leqProd leqFP leqGP p q || leqProd leqFP leqGP q p }
@-}
leqProdTotal :: Eq (f p) => (f p -> f p -> Bool) -> (f p -> f p -> Proof)
             -> (g p -> g p -> Bool) -> (g p -> g p -> Proof)
             -> Product f g p -> Product f g p -> Proof
leqProdTotal leqFP leqFPTotal leqGP leqGPTotal p@(Product x1 y1) q@(Product x2 y2) =
      (leqProd leqFP leqGP p q || leqProd leqFP leqGP q p)
  ==. ((if x1 == x2 then leqGP y1 y2 else leqFP x1 x2) || (if x2 == x1 then leqGP y2 y1 else leqFP x2 x1))
  ==. ((if x1 == x2 then leqGP y1 y2 else leqFP x1 x2) || (if x1 == x2 then leqGP y2 y1 else leqFP x2 x1))
  ==. (if x1 == x2 then leqGP y1 y2 || leqGP y2 y1 else leqFP x1 x2 || leqFP x2 x1)
  ==. (if x1 == x2 then True else leqFP x1 x2 || leqFP x2 x1) ? leqGPTotal y1 y2
  ==. (if x1 == x2 then True else True)                       ? leqFPTotal x1 x2
  ==. True
  *** QED

vordProd :: (Eq (f p), Eq (g p)) => VerifiedOrd (f p) -> VerifiedOrd (g p) -> VerifiedOrd (Product f g p)
vordProd (VerifiedOrd leqFP leqFPRefl leqFPAntisym leqFPTrans leqFPTotal) (VerifiedOrd leqGP leqGPRefl leqGPAntisym leqGPTrans leqGPTotal) =
    VerifiedOrd
        (leqProd leqFP leqGP)
        (leqProdRefl leqFP leqFPRefl leqGP leqGPRefl)
        (leqProdAntisym leqFP leqFPAntisym leqGP leqGPAntisym)
        (leqProdTrans leqFP leqFPAntisym leqFPTrans leqGP leqGPTrans)
        (leqProdTotal leqFP leqFPTotal leqGP leqGPTotal)
