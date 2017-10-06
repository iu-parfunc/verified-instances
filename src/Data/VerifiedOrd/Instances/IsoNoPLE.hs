{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}

module Data.VerifiedOrd.Instances.Iso (vordIso) where

import Data.Inj
import Data.Iso
import Data.VerifiedEq.Instances.Contra
import Data.VerifiedOrd
import Data.VerifiedOrd.Instances.Inj
import Language.Haskell.Liquid.ProofCombinators

{-# INLINE vordIso #-}
vordIso :: Iso a b -> VerifiedOrd a -> VerifiedOrd b
vordIso iso@(Iso _ f _ _) ord@(VerifiedOrd _ _ _ _ _ veqa) =
  vordInj (fromIsoR (veqContra f veqa) iso) ord
