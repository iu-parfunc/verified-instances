{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--totality"    @-}

module GHC.Classes.VerifiedOrd where

import Language.Haskell.Liquid.ProofCombinators

class (Ord a) => VerifiedOrd a where
