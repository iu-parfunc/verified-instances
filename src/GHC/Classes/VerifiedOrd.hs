{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--totality"    @-}

module GHC.Classes.VerifiedOrd where

class (Ord a) => VerifiedOrd a where
