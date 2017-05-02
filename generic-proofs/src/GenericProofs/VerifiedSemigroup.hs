{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--totality"       @-}
{-@ LIQUID "--exactdc"        @-}
module GenericProofs.VerifiedSemigroup where

import GenericProofs.Iso
import Language.Haskell.Liquid.ProofCombinators

{-@ data VerifiedSemigroup a = VerifiedSemigroup {
        sappend :: a -> a -> a
      , sappendAssoc :: x:a -> y:a -> z:a
                     -> { sappend x (sappend y z) == sappend (sappend x y) z }
      }
@-}
data VerifiedSemigroup a = VerifiedSemigroup {
    sappend      :: a -> a -> a
  , sappendAssoc :: a -> a -> a -> Proof
  }
infixr 6 `sappend`

{-@ axiomatize sappendInv @-}
sappendInv :: (a -> a -> a)
           -> (a -> b) -> (b -> a)
           -> b -> b -> b
sappendInv sappendA f g x y = f (sappendA (g x) (g y))
{-# INLINE sappendInv #-}

{-@ sappendInvAssoc :: sappendA:(a -> a -> a)
                    -> sappendAAssoc:(i:a -> j:a -> k:a -> { sappendA i (sappendA j k) == sappendA (sappendA i j) k })
                    -> f:(a -> b)
                    -> g:(b -> a)
                    -> gof:(z:a -> { g (f z) == z })
                    -> x:b
                    -> y:b
                    -> z:b
                    -> { sappendInv sappendA f g x (sappendInv sappendA f g y z) == sappendInv sappendA f g (sappendInv sappendA f g x y) z }
@-}
sappendInvAssoc :: (a -> a -> a)
                -> (a -> a -> a -> Proof)
                -> (a -> b)
                -> (b -> a)
                -> (a -> Proof)
                -> b -> b -> b
                -> Proof
sappendInvAssoc sappendA sappendAAssoc f g gof x y z
  =   sappendInv sappendA f g x (sappendInv sappendA f g y z)
  ==. sappendInv sappendA f g x (f (sappendA (g y) (g z)))
  ==. f (sappendA (g x) (g (f (sappendA (g y) (g z)))))
  ==. f (sappendA (g x) (sappendA (g y) (g z))) ? gof (sappendA (g y) (g z))
  ==. f (sappendA (sappendA (g x) (g y)) (g z)) ? sappendAAssoc (g x) (g y) (g z)
  ==. f (sappendA (g (f (sappendA (g x) (g y)))) (g z)) ? gof (sappendA (g x) (g y))
  ==. f (sappendA (g (sappendInv sappendA f g x y)) (g z))
  ==. sappendInv sappendA f g (sappendInv sappendA f g x y) z
  *** QED

{-@ vsemigroupInv :: f:(a -> b)
                  -> g:(b -> a)
                  -> gof:(x:a -> { g (f x) == x })
                  -> VerifiedSemigroup a
                  -> VerifiedSemigroup b
@-}
vsemigroupInv :: (a -> b) -> (b -> a) -> (a -> Proof)
              -> VerifiedSemigroup a -> VerifiedSemigroup b
vsemigroupInv f g gof (VerifiedSemigroup sappendA sappendAAssoc)
  = VerifiedSemigroup (sappendInv      sappendA f g)
                      (sappendInvAssoc sappendA sappendAAssoc f g gof)

vsemigroupIso :: Iso a b -> VerifiedSemigroup a -> VerifiedSemigroup b
vsemigroupIso (Iso f g _ gof) = vsemigroupInv f g gof
