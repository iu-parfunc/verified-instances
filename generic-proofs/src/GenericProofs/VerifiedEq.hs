{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--totality"       @-}
{-@ LIQUID "--exactdc"        @-}
module GenericProofs.VerifiedEq where

import Data.Functor.Contravariant
import GenericProofs.Iso
import Language.Haskell.Liquid.ProofCombinators

{-@ data VerifiedEq a = VerifiedEq {
      eq :: a -> a -> Bool
    , refl :: x:a -> { v:() | eq x x }
    , sym :: x:a -> y:a -> { v:() | eq x y ==> eq y x }
    , trans :: x:a -> y:a -> z:a -> { v:() | eq x y && eq y z ==> eq x z }
    }
@-}

data VerifiedEq a = VerifiedEq {
    eq    :: a -> a -> Bool
  , refl  :: a -> Proof
  , sym   :: a -> a -> Proof
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
veqContra g p = VerifiedEq (eqContra eqa g) (eqContraRefl eqa eqaRefl g) (eqContraSym eqa eqaSym g) (eqContraTrans eqa eqaTrans g)
  where
    eqa      = getEq    p
    eqaRefl  = getRefl  p
    eqaSym   = getSym   p
    eqaTrans = getTrans p

{-@ measure eq @-}
{-@ getEq :: p:VerifiedEq a -> {f:(a -> a -> Bool) | f = eq p} @-}
getEq :: VerifiedEq a -> (a -> a -> Bool)
getEq (VerifiedEq a _ _ _) = a

{-@ getRefl :: p:VerifiedEq a -> x:a -> { eq p x x } @-}
getRefl :: VerifiedEq a -> a -> Proof
getRefl (VerifiedEq _ r _ _) = r

{-@ getSym :: p:VerifiedEq a -> x:a -> y:a -> { eq p x y => eq p y x } @-}
getSym :: VerifiedEq a -> a -> a -> Proof
getSym (VerifiedEq _ _ s _) = s

{-@ assume getTrans :: p:VerifiedEq a -> x:a -> y:a -> z:a -> { eq p x y && eq p y z => eq p x z } @-}
getTrans :: VerifiedEq a -> a -> a -> a -> Proof
getTrans (VerifiedEq _ _ _ t) = t

instance Contravariant VerifiedEq where
  contramap = veqContra

veqIso :: Iso a b -> VerifiedEq a -> VerifiedEq b
veqIso (Iso _ f _ _) = veqContra f
{-# INLINE veqIso #-}
