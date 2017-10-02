{-@ LIQUID "--higherorder" @-}

module GHC.Classes.VerifiedOrd where

class (Ord a) => VerifiedOrd a where
