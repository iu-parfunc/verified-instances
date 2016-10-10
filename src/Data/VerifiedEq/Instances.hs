{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}

module Data.VerifiedEq.Instances where

import Data.VerifiedEq
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize eqProd @-}
eqProd :: (a -> a -> Bool) -> (b -> b -> Bool)
       -> (a, b) -> (a, b) -> Bool
eqProd eqa eqb p q =
  eqa (fst p) (fst q) && eqb (snd p) (snd q)

{-@ eqProdRefl :: eqa:(a -> a -> Bool) -> eqaRefl:(x:a -> { Prop (eqa x x) })
               -> eqb:(b -> b -> Bool) -> eqbRefl:(y:b -> { Prop (eqb y y) })
               -> p:(a, b)
               -> { eqProd eqa eqb p p }
@-}
eqProdRefl :: (a -> a -> Bool) -> (a -> Proof)
           -> (b -> b -> Bool) -> (b -> Proof)
           -> (a, b) -> Proof
eqProdRefl eqa eqaRefl eqb eqbRefl p@(x, y) =
      eqProd eqa eqb p p
  ==. (eqa (fst p) (fst p) && eqb (snd p) (snd p))
  ==. (eqa x x && eqb y y)
  ==. (True && eqb y y) ? eqaRefl x
  ==. (True && True)    ? eqbRefl y
  ==. True
  *** QED
