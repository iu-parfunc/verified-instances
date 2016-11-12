{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}

module GHC.Classes.VerifiedEq where

import Language.Haskell.Liquid.ProofCombinators

{-@ class (Eq a) => VerifiedEq a where
      eq :: a -> a -> Bool
      refl :: x:a -> { v:() | Prop (eq x x) }
      sym :: x:a -> y:a -> { v:() | Prop (eq x y) ==> Prop (eq y x) }
      trans :: x:a -> y:a -> z:a -> { v:() | Prop (eq x y) && Prop (eq y z) ==> Prop (eq x z) }
@-}
class Eq a => VerifiedEq a where
  eq :: a -> a -> Bool
  eq = (==)
  refl :: a -> Proof
  sym :: a -> a -> Proof
  trans :: a -> a -> a -> Proof

{-@ axiomatize eqInt @-}
eqInt :: Int -> Int -> Bool
eqInt x y = x == y

{-@ eqIntRefl :: x:Int -> { eqInt x x } @-}
eqIntRefl :: Int -> Proof
eqIntRefl x = eqInt x x *** QED

{-@ eqIntSym :: x:Int -> y:Int -> { eqInt x y ==> eqInt y x } @-}
eqIntSym :: Int -> Int -> Proof
eqIntSym x y = eqInt x y *** QED

{-@ eqIntTrans :: x:Int -> y:Int -> z:Int -> { eqInt x y && eqInt y z ==> eqInt x z } @-}
eqIntTrans :: Int -> Int -> Int -> Proof
eqIntTrans x y z = eqInt x y && eqInt y z *** QED

instance VerifiedEq Int where
  {-@ define $ceq = eqInt @-}
  refl = eqIntRefl
  sym = eqIntSym
  trans = eqIntTrans
