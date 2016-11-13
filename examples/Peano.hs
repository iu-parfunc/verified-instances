{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}

module Peano where

import Data.Iso
import Language.Haskell.Liquid.ProofCombinators

{-@ data Peano [toNat] = Z | S Peano @-}
data Peano = Z | S Peano

{-@ type Nat = { v:Int | 0 <= v } @-}
type Nat = Int

{-@ measure toNat @-}
{-@ axiomatize toNat @-}
{-@ toNat :: Peano -> Nat @-}
toNat :: Peano -> Nat
toNat Z     = 0
toNat (S n) = 1 + toNat n

{-@ axiomatize fromNat @-}
{-@ fromNat :: Nat -> Peano @-}
fromNat :: Nat -> Peano
fromNat n
  | n == 0 = Z
  | otherwise = S (fromNat (n - 1))

{-@ toFrom :: x:Nat -> { toNat (fromNat x) == x } @-}
toFrom :: Nat -> Proof
toFrom n
  | n == 0 = toNat (fromNat 0) ==. toNat Z ==. 0 *** QED
  | n > 0 = toNat (fromNat n)
        ==. toNat (S (fromNat (n - 1)))
        ==. 1 + toNat (fromNat (n - 1))
        ==. 1 + (n - 1) ? toFrom (n - 1)
        ==. n
        *** QED

{-@ fromTo :: x:Peano -> { fromNat (toNat x) == x } @-}
fromTo :: Peano -> Proof
fromTo Z = fromNat (toNat Z) ==. fromNat 0 ==. Z *** QED
fromTo (S n) = fromNat (toNat (S n))
           ==. fromNat (1 + toNat n)
           ==. S (fromNat ((1 + toNat n) - 1))
           ==. S (fromNat (toNat n))
           ==. S n ? fromTo n
           *** QED

{-@ isoPeanoNat :: Iso Peano Nat @-}
isoPeanoNat :: Iso Peano Nat
isoPeanoNat = Iso toNat fromNat toFrom fromTo
