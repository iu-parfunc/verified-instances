{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}

module Data.VerifiedEq.Instances.Iso (veqIso) where

import Data.Iso
import Data.VerifiedEq
import Data.VerifiedEq.Instances.Contra
import Language.Haskell.Liquid.ProofCombinators

veqIso :: Iso a b -> VerifiedEq a -> VerifiedEq b
veqIso (Iso _ f _ _) = veqContra f
{-# INLINE veqIso #-}
