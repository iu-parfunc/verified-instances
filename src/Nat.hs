{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorderqs"   @-}
{-@ LIQUID "--prune-unsorted"  @-}

module Nat where

import VerifiedEq
import ProofCombinators

{-@ data N [toInt] = Zero | Suc N @-}
data N = Zero | Suc N

{-@ measure toInt @-}
{-@ toInt :: N -> Nat @-}
toInt :: N -> Int
toInt Zero = 0
toInt (Suc n) = 1 + toInt n

{-@ axiomatize eqN @-}
eqN :: N -> N -> Bool
eqN Zero Zero = True
eqN (Suc m) (Suc n) = eqN m n
eqN _ _ = False

{-@ eqNRefl :: x:N -> { eqN x x } @-}
eqNRefl :: N -> Proof
eqNRefl Zero =   eqN Zero Zero
             ==. True
             *** QED
eqNRefl (Suc n) =   eqN (Suc n) (Suc n)
                ==. eqN n n
                ==. True ? eqNRefl n
                *** QED

{-@ eqNSym :: x:N -> y:N -> { eqN x y ==> eqN y x } @-}
eqNSym :: N -> N -> Proof
eqNSym Zero Zero = simpleProof
eqNSym Zero (Suc y) =   eqN Zero (Suc y)
                    ==. False
                    *** QED
eqNSym (Suc x) Zero =   eqN (Suc x) Zero
                    ==. False
                    *** QED
eqNSym (Suc x) (Suc y) =   eqN (Suc x) (Suc y)
                       ==. eqN x y
                       ==. eqN y x ? eqNSym x y
                       ==. eqN (Suc y) (Suc x)
                       *** QED

{-@ eqNTrans :: x:N -> y:N -> z:N -> { eqN x y && eqN y z ==> eqN x z } @-}
eqNTrans :: N -> N -> N -> Proof
eqNTrans Zero Zero Zero = simpleProof
eqNTrans Zero Zero (Suc z) = simpleProof
eqNTrans Zero (Suc y) z =   (eqN Zero (Suc y) && eqN (Suc y) z)
                        ==. False
                        *** QED
eqNTrans (Suc x) Zero z =   (eqN (Suc x) Zero && eqN Zero z)
                        ==. False
                        *** QED
eqNTrans (Suc x) (Suc y) Zero =   (eqN (Suc x) (Suc y) && eqN (Suc y) Zero)
                              ==. False
                              *** QED
eqNTrans (Suc x) (Suc y) (Suc z) =   (eqN (Suc x) (Suc y) && eqN (Suc y) (Suc z))
                                 ==. (eqN x y && eqN y z)
                                 ==. eqN x z ? eqNTrans x y z
                                 ==. eqN (Suc x) (Suc z)
                                 *** QED

instance Eq N where
  (==) = eqN

-- instance VerifiedEq N where
--   refl = eqNRefl
--   sym = undefined
--   trans = undefined
