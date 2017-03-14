{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--totality"       @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--exactdc"        @-}
module GenericProofs.VerifiedEq where

import Data.Functor.Contravariant
import GenericProofs.Combinators
import GenericProofs.Iso

{-@ data VerifiedEq a = VerifiedEq {
      eq :: a -> a -> Bool
    , refl :: x:a -> { v:() | eq x x }
    , sym :: x:a -> y:a -> { v:() | eq x y ==> eq y x }
    , trans :: x:a -> y:a -> z:a -> { v:() | eq x y && eq y z ==> eq x z }
    }
@-}

data VerifiedEq a = VerifiedEq {
    eq :: a -> a -> Bool
  , refl :: a -> Proof
  , sym :: a -> a -> Proof
  , trans :: a -> a -> a -> Proof
  }

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
eqContraRefl eqa eqaRefl g x =
      eqContra eqa g x x
  ==. eqa (g x) (g x)
  ==. True ? eqaRefl (g x)
  *** QED

{-@ eqContraSym :: eqa:(a -> a -> Bool) -> eqaSym:(x:a -> y:a -> { eqa x y ==> eqa y x })
                -> g:(b -> a) -> x:b -> y:b -> { eqContra eqa g x y ==> eqContra eqa g y x }
@-}
eqContraSym :: (a -> a -> Bool) -> (a -> a -> Proof)
            -> (b -> a) -> b -> b -> Proof
eqContraSym eqa eqaSym g x y =
      eqContra eqa g x y
  ==. eqa (g x) (g y)
  ==. eqa (g y) (g x) ? eqaSym (g x) (g y)
  ==. eqContra eqa g y x
  *** QED

{-@ eqContraTrans :: eqa:(a -> a -> Bool) -> eqaTrans:(x:a -> y:a -> z:a -> { eqa x y && eqa y z ==> eqa x z })
                  -> g:(b -> a) -> x:b -> y:b -> z:b -> { eqContra eqa g x y && eqContra eqa g y z ==> eqContra eqa g x z }
@-}
eqContraTrans :: (a -> a -> Bool) -> (a -> a -> a -> Proof)
              -> (b -> a) -> b -> b -> b -> Proof
eqContraTrans eqa eqaTrans g x y z =
      (eqContra eqa g x y && eqContra eqa g y z)
  ==. (eqa (g x) (g y) && eqa (g y) (g z))
  ==. eqa (g x) (g z) ? eqaTrans (g x) (g y) (g z)
  ==. eqContra eqa g x z
  *** QED

veqContra :: (b -> a) -> VerifiedEq a -> VerifiedEq b
veqContra g (VerifiedEq eqa eqaRefl eqaSym eqaTrans) =
  VerifiedEq (eqContra eqa g) (eqContraRefl eqa eqaRefl g) (eqContraSym eqa eqaSym g) (eqContraTrans eqa eqaTrans g)

instance Contravariant VerifiedEq where
  contramap = veqContra

veqIso :: Iso a b -> VerifiedEq a -> VerifiedEq b
veqIso (Iso _ f _ _) = veqContra f
{-# INLINE veqIso #-}
