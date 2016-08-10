{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--totality"    @-}

module VerifiedOrd where

import ProofCombinators

class (Ord a) => VerifiedOrd a where
