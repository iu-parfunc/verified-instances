{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}

module GHC.Classes.VerifiedEq where

import Language.Haskell.Liquid.ProofCombinators

{-@ class (Eq a) => VerifiedEq a where
      eq :: a -> a -> Bool
      refl :: x:a -> { v:() | Prop (eq x x) }
      sym :: x:a -> y:a -> { v:() | Prop (eq x y) ==> Prop (eq y x) }
      trans :: x:a -> y:a -> z:a -> { v:() | Prop (eq x y) && Prop (eq y z) ==> Prop (eq y x) }
@-}
class Eq a => VerifiedEq a where
  eq :: a -> a -> Bool
  eq = (==)
  refl :: a -> Proof
  sym :: a -> a -> Proof
  trans :: a -> a -> a -> Proof

{-@ eqIntRefl :: x:Int -> { x == x } @-}
eqIntRefl :: Int -> Proof
eqIntRefl _x = simpleProof

{-@ eqIntSym :: x:Int -> y:Int -> { x == y ==> y == x } @-}
eqIntSym :: Int -> Int -> Proof
eqIntSym _x _y = simpleProof

{-@ eqIntTrans :: x:Int -> y:Int -> z:Int -> { x == y && y == z ==> x == z } @-}
eqIntTrans :: Int -> Int -> Int -> Proof
eqIntTrans _x _y _z = simpleProof

-- instance VerifiedEq Int where
--   refl = eqIntRefl
--   sym = eqIntSym
--   trans = eqIntTrans
