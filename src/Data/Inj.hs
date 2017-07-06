{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}

module Data.Inj (Inj(..), fromIsoL, fromIsoR) where

import Data.Iso
import Data.VerifiableConstraint
import Data.VerifiedEq
import Data.VerifiedEq.Instances.Contra
import Language.Haskell.Liquid.ProofCombinators

{-@ data Inj a b = Inj { f  :: a -> b
                       , inj :: x:a -> y:{a | f x == f y} -> { x == y }
                       }
@-}

data Inj a b = Inj { f   :: a -> b
                   , inj :: a -> a -> Proof
                   }

{-@ fromInj :: from:(b -> a) -> to:(a -> b)
            -> fot:(x:a -> { from (to x) == x })
            -> x:a -> y:{a | to x == to y} -> { x == y }
@-}
fromInj :: (b -> a) -> (a -> b)
        -> (a -> Proof)
        -> a -> a -> Proof
fromInj from to fot x y =
  [ fot x, fot y] *** QED

fromIsoL :: VerifiedEq a -> Iso a b -> Inj a b
fromIsoL veqa (Iso t f tof fot) = Inj t (fromInj f t fot)

fromIsoR :: VerifiedEq b -> Iso a b -> Inj b a
fromIsoR veqb (Iso t f tof fot) = Inj f (fromInj t f tof)
