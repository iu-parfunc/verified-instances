{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}

module Data.VerifiedMonoid.Instances.Iso (vmonoidIso) where

import Data.Iso
import Data.VerifiedMonoid
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize identTo @-}
identTo :: a -> (a -> b) -> b
identTo x to = to x
{-# INLINE identTo #-}

{-@ axiomatize prodIso @-}
prodIso :: (a -> a -> a)
        -> (a -> b) -> (b -> a)
        -> (b -> b -> b)
prodIso proda to from x y = to (proda (from x) (from y))
{-# INLINE prodIso #-}

{-@ lidentIso :: identa:a -> proda:(a -> a -> a)
              -> lidenta:(x:a -> { proda identa x == x })
              -> to:(a -> b) -> from:(b -> a)
              -> tof:(x:b -> { to (from x) == x })
              -> fot:(x:a -> { from (to x) == x })
              -> x:b -> { prodIso proda to from (identTo identa to) x == x }
@-}
lidentIso :: a -> (a -> a -> a)
          -> (a -> Proof)
          -> (a -> b) -> (b -> a)
          -> (b -> Proof) -> (a -> Proof)
          -> b -> Proof
lidentIso identa proda lidenta to from tof fot x =
      prodIso proda to from (identTo identa to) x
  ==. prodIso proda to from (to identa) x
  ==. to (proda (from (to identa)) (from x)) ? fot identa
  ==. to (proda identa (from x)) ? lidenta (from x)
  ==. to (from x) ? tof x
  ==. x
  *** QED

{-@ ridentIso :: identa:a -> proda:(a -> a -> a)
              -> ridenta:(x:a -> { proda x identa == x })
              -> to:(a -> b) -> from:(b -> a)
              -> tof:(x:b -> { to (from x) == x })
              -> fot:(x:a -> { from (to x) == x })
              -> x:b -> { prodIso proda to from x (identTo identa to) == x }
@-}
ridentIso :: a -> (a -> a -> a)
          -> (a -> Proof)
          -> (a -> b) -> (b -> a)
          -> (b -> Proof) -> (a -> Proof)
          -> b -> Proof
ridentIso identa proda ridenta to from tof fot x =
      prodIso proda to from x (identTo identa to)
  ==. prodIso proda to from (to identa) x
  ==. to (proda (from (to identa)) (from x)) ? fot identa
  ==. to (proda identa (from x)) ? ridenta (from x)
  ==. to (from x) ? tof x
  ==. x
  *** QED

{-@ assocIso :: proda:(a -> a -> a)
             -> assoca:(a -> a -> a -> Proof)
             -> to:(a -> b) -> from:(b -> a)
             -> tof:(x:b -> { to (from x) == x })
             -> fot:(x:a -> { from (to x) == x })
             -> x:b -> y:b -> z:b
             -> { prodIso proda to from x (prodIso proda to from y z)
               == prodIso proda to from (prodIso proda to from x y) z }
@-}
assocIso :: (a -> a -> a) -> (a -> a -> a -> Proof)
         -> (a -> b) -> (b -> a)
         -> (b -> Proof) -> (a -> Proof)
         -> b -> b -> b -> Proof
assocIso proda assoca to from tof fot x y z =
      prodIso proda to from x (prodIso proda to from y z)
  ==. prodIso proda to from x (to (proda (from y) (from z)))
  ==. to (proda (from x) (from (to (proda (from y) (from z)))))
  ==. to (proda (from x) (proda (from y) (from z))) ? fot (proda (from y) (from z))
  ==. to (proda (proda (from x) (from y)) (from z)) ? assoca (from x) (from y) (from z)
  ==. to (proda (from (to (proda (from x) (from y)))) (from z)) ? fot (proda (from x) (from y))
  ==. to (proda (from (prodIso proda to from x y)) (from z))
  ==. prodIso proda to from (prodIso proda to from x y) z
  *** QED

vmonoidIso :: Iso a b -> VerifiedMonoid a -> VerifiedMonoid b
vmonoidIso (Iso to from tof fot) (VerifiedMonoid identa proda lidenta ridenta assoca) =
  VerifiedMonoid
    (identTo identa to)
    (prodIso proda to from)
    (lidentIso identa proda lidenta to from tof fot)
    (ridentIso identa proda ridenta to from tof fot)
    (assocIso proda assoca to from tof fot)
