{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}

module Data.Inj (Inj(..), fromIsoL, fromIsoR) where

import Data.Iso
import Data.VerifiableConstraint
import Data.VerifiedEq
import Data.VerifiedEq.Instances.Contra
import Language.Haskell.Liquid.ProofCombinators

{-@ data Inj a b = Inj { to  :: a -> b
                       , inj :: x:a -> y:a -> { to x == to y ==> x == y }
                       }
@-}

data Inj a b = Inj { to  :: a -> b
                   , inj :: a -> a -> Proof
                   }

{-@ fromInj :: from:(b -> a) -> to:(a -> b)
            -> fot:(x:a -> { from (to x) == x })
            -> VerifiedEq a
            -> x:a -> y:a -> { to x == to y ==> x == y }
@-}
fromInj :: (b -> a) -> (a -> b)
        -> (a -> Proof)
        -> VerifiedEq a
        -> a -> a -> Proof
fromInj from to fot veqa x y =
      using (VEq veqa)
    $ using (VEq $ veqContra from veqa)
    $ to x == to y
  ==. from (to x) == from (to y)
  ==. x == from (to y) ? fot x
  ==. x == y           ? fot y
  *** QED

fromIsoL :: VerifiedEq a -> Iso a b -> Inj a b
fromIsoL veqa (Iso t f tof fot) =
  Inj t (fromInj f t fot veqa)

fromIsoR :: VerifiedEq b -> Iso a b -> Inj b a
fromIsoR veqb (Iso t f tof fot) =
  Inj f (fromInj t f tof veqb)
