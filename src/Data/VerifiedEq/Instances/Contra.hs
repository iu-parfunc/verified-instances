{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Data.VerifiedEq.Instances.Contra (veqContra, eqContra) where

import Data.Functor.Contravariant
import Data.VerifiedEq
import Language.Haskell.Liquid.ProofCombinators
qed _ = ()

{-@ axiomatize eqContra @-}
eqContra :: (a -> a -> Bool)
         -> (b -> a)
         -> (b -> b -> Bool)
eqContra eqa g x y = eqa (g x) (g y)
{-# INLINE eqContra #-}

{-@ eqContraRefl :: eqa:(a -> a -> Bool) -> eqaRefl:(x:a -> { eqa x x })
                 -> g:(b -> a) -> x:b -> { eqContra eqa g x x }
@-}
eqContraRefl :: (a -> a -> Bool) -> (a -> Proof)
             -> (b -> a) -> b -> Proof
eqContraRefl eqa eqaRefl g x = eqaRefl (g x) *** QED

{-@ eqContraSym :: eqa:(a -> a -> Bool) -> eqaSym:(x:a -> y:{a | eqa x y } -> { eqa y x })
                -> g:(b -> a) -> x:b -> y:{b | eqContra eqa g x y } -> { eqContra eqa g y x }
@-}
eqContraSym :: (a -> a -> Bool) -> (a -> a -> Proof)
            -> (b -> a) -> b -> b -> Proof
eqContraSym eqa eqaSym g x y = qed [ eqaSym (g x) (g y) ]

{-@ eqContraTrans :: eqa:(a -> a -> Bool) -> eqaTrans:(x:a -> y:a -> z:{a | eqa x y && eqa y z } -> { eqa x z })
                  -> g:(b -> a) -> x:b -> y:b -> z:{b | eqContra eqa g x y && eqContra eqa g y z } -> { eqContra eqa g x z }
@-}
eqContraTrans :: (a -> a -> Bool) -> (a -> a -> a -> Proof)
              -> (b -> a) -> b -> b -> b -> Proof
eqContraTrans eqa eqaTrans g x y z = qed [eqaTrans (g x) (g y) (g z)]

veqContra :: (b -> a) -> VerifiedEq a -> VerifiedEq b
veqContra g (VerifiedEq eqa eqaRefl eqaSym eqaTrans) =
  VerifiedEq (eqContra eqa g) (eqContraRefl eqa eqaRefl g) (eqContraSym eqa eqaSym g) (eqContraTrans eqa eqaTrans g)

instance Contravariant VerifiedEq where
  contramap = veqContra
