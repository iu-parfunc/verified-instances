{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}

module Data.VerifiedEq.Instances.Iso (veqIso) where

import Data.Functor.Contravariant
import Data.Iso
import Data.VerifiedEq
import Data.VerifiedEq.Instances.Contra
import Language.Haskell.Liquid.ProofCombinators

veqIso :: Iso a b -> VerifiedEq a -> VerifiedEq b
veqIso (Iso _ from _ _) = contramap from
