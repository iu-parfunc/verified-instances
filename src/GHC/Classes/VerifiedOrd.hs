{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--totality"    @-}

module GHC.Classes.VerifiedOrd where

import GHC.Classes.VerifiedEq
import Language.Haskell.Liquid.ProofCombinators

{-@
class (Ord a, VerifiedEq a) =>
      VerifiedOrd a where
  leq :: a -> a -> Bool
  refl :: x:a -> { v:() | Prop (leq x x) }
  antisym :: x:a -> y:a -> { v:() | Prop (leq x y) && Prop (leq y x) ==> x == y }
  trans :: x:a -> y:a -> z:a -> { v:() | Prop (leq x y) && Prop (leq y z) ==> Prop (leq x z) }
  total :: x:a -> y:a -> { v:() | Prop (leq x y) || Prop (leq y x) }
@-}
class (Ord a, VerifiedEq a) =>
      VerifiedOrd a where
  leq :: a -> a -> Bool
  leq = (<=)
  refl :: a -> Proof
  antisym :: a -> a -> Proof
  trans :: a -> a -> a -> Proof
  total :: a -> a -> Proof

{-@ axiomatize leqInt @-}
leqInt :: Int -> Int -> Bool
leqInt x y = x <= y

{-@ leqIntRefl :: x:Int -> { leqInt x x } @-}
leqIntRefl :: Int -> Proof
leqIntRefl x = leqInt x x *** QED

{-@ leqIntAntisym :: x:Int -> y:Int -> { leqInt x y && leqInt y x ==> x == y } @-}
leqIntAntisym :: Int -> Int -> Proof
leqIntAntisym x y = leqInt x y && leqInt y x *** QED

{-@ leqIntTrans :: x:Int -> y:Int -> z:Int -> { leqInt x y && leqInt y z ==> leqInt x z } @-}
leqIntTrans :: Int -> Int -> Int -> Proof
leqIntTrans x y z = (leqInt x y && leqInt y z) ==. leqInt x z *** QED

{-@ leqIntTotal :: x:Int -> y:Int -> { leqInt x y || leqInt y x } @-}
leqIntTotal :: Int -> Int -> Proof
leqIntTotal x y = (leqInt x y || leqInt y x) *** QED

instance VerifiedOrd Int where
  {-@ define $cleq = leqInt @-}
  refl = leqIntRefl
  antisym = leqIntAntisym
  trans = leqIntTrans
  total = leqIntTotal
