{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}

module Data.VerifiedEq.Instances.Iso (veqIso) where

import Data.Iso
import Data.VerifiedEq
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize eqIso @-}
eqIso :: (a -> a -> Bool)
      -> (b -> a) -> b -> b -> Bool
eqIso eqa g x y = eqa (g x) (g y)

{-@ eqIsoRefl :: eqa:(a -> a -> Bool) -> eqaRefl:(x:a -> { Prop (eqa x x) })
              -> g:(b -> a) -> x:b -> { eqIso eqa g x x }
@-}
eqIsoRefl :: (a -> a -> Bool) -> (a -> Proof)
          -> (b -> a) -> b -> Proof
eqIsoRefl eqa eqaRefl g x =
      eqIso eqa g x x
  ==. eqa (g x) (g x)
  ==. True ? eqaRefl (g x)
  *** QED

{-@ eqIsoSym :: eqa:(a -> a -> Bool) -> eqaSym:(x:a -> y:a -> { Prop (eqa x y) ==> Prop (eqa y x) })
             -> g:(b -> a) -> x:b -> y:b -> { eqIso eqa g x y ==> eqIso eqa g y x }
@-}
eqIsoSym :: (a -> a -> Bool) -> (a -> a -> Proof)
         -> (b -> a) -> b -> b -> Proof
eqIsoSym eqa eqaSym g x y =
      eqIso eqa g x y
  ==. eqa (g x) (g y)
  ==. eqa (g y) (g x) ? eqaSym (g x) (g y)
  ==. eqIso eqa g y x
  *** QED

{-@ eqIsoTrans :: eqa:(a -> a -> Bool) -> eqaTrans:(x:a -> y:a -> z:a -> { Prop (eqa x y) && Prop (eqa y z) ==> Prop (eqa x z) })
               -> g:(b -> a) -> x:b -> y:b -> z:b -> { eqIso eqa g x y && eqIso eqa g y z ==> eqIso eqa g x z }
@-}
eqIsoTrans :: (a -> a -> Bool) -> (a -> a -> a -> Proof)
           -> (b -> a) -> b -> b -> b -> Proof
eqIsoTrans eqa eqaTrans g x y z =
      (eqIso eqa g x y && eqIso eqa g y z)
  ==. (eqa (g x) (g y) && eqa (g y) (g z))
  ==. eqa (g x) (g z) ? eqaTrans (g x) (g y) (g z)
  ==. eqIso eqa g x z
  *** QED

veqIso :: Iso a b -> VerifiedEq a -> VerifiedEq b
veqIso (Iso f g fog gof) (VerifiedEq eqa eqaRefl eqaSym eqaTrans) =
  VerifiedEq (eqIso eqa g) (eqIsoRefl eqa eqaRefl g) (eqIsoSym eqa eqaSym g) (eqIsoTrans eqa eqaTrans g)
