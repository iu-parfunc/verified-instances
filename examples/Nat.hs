{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--exact-data-cons" @-}

module Nat where

-- import Data.VerifiedEq
import GHC.Classes.VerifiedEq
import Language.Haskell.Liquid.ProofCombinators

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

{-@ eqNTrans :: x:N -> y:N -> z:N -> { (eqN x y && eqN y z) ==> eqN x z } @-}
eqNTrans :: N -> N -> N -> Proof
eqNTrans Zero Zero Zero = simpleProof
eqNTrans Zero Zero (Suc _) = simpleProof
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

instance VerifiedEq N where
  {-@ define $ceq = eqN @-}
  eq   = eqN 
  refl = eqNRefl
  sym = eqNSym
  trans = eqNTrans

-- veqN :: VerifiedEq N
-- veqN = VerifiedEq eqN eqNRefl eqNSym eqNTrans

{-@ axiomatize addN @-}
addN :: N -> N -> N
addN Zero y = y
addN (Suc x) y = Suc (x `addN` y)

{-@ addNAssoc :: x:N -> y:N -> z:N -> { (addN (addN x y) z) == (addN x (addN y z)) } @-}
addNAssoc :: N -> N -> N -> Proof
addNAssoc Zero y z =   (addN (addN Zero y) z)
                  ==. addN y z
                  ==. addN Zero (addN y z)
                  *** QED
addNAssoc (Suc x) y z =   (addN (addN (Suc x) y) z)
                     ==. (addN (Suc (addN x y)) z)
                     ==. (Suc (addN (addN x y) z))
                     ==. (Suc (addN x (addN y z))) ? addNAssoc x y z
                     ==. (addN (Suc x) (addN y z))
                     *** QED
