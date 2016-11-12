{-@ LIQUID "--higherorder"        @-}
{- LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}

import Language.Haskell.Liquid.ProofCombinators


data N = Z | S N 
{-@ data N [toInt] = Z | S N @-}

{-@ measure toInt @-}
{-@ toInt :: N -> Nat @-}
toInt :: N -> Int 
toInt Z = 0 
toInt (S n) = 1 + toInt n 

{-@ reflect natleq @-}
natleq :: N -> N -> Bool 
natleq Z _ = True 
natleq _ Z = False 
natleq (S n) (S m) = natleq n m

{-@ totalNat :: n:N -> m:N -> {(natleq n m) || (natleq m n)} / [toInt n + toInt m] @-}
totalNat :: N -> N -> Proof 
totalNat Z m = natleq Z m *** QED 
totalNat n Z = natleq Z n *** QED 
totalNat (S n) (S m) 
  =   (natleq (S n) (S m) || natleq (S m) (S n))
  ==. (natleq n m || natleq (S m) (S n)) ? (totalNat n m ) 
  ==. (natleq n m || natleq m n) ? (totalNat m n) 
  *** QED 

