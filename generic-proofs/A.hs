-- A.hs
{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--i=./include"        @-}
module A where

import Language.Haskell.Liquid.ProofCombinators

import Generics.Deriving.Newtypeless


{-@ axiomatize eqK1 @-}
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
