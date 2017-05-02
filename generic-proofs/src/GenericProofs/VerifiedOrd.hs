{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
module GenericProofs.VerifiedOrd (VerifiedOrd(..)) where

import Language.Haskell.Liquid.ProofCombinators

{-@ data VerifiedOrd a = VerifiedOrd {
      leq :: (a -> a -> Bool)
    , refl :: (x:a -> { leq x x })
    , antisym :: (x:a -> y:a -> { leq x y && leq y x ==> x == y })
    , trans :: (x:a -> y:a -> z:a -> { leq x y && leq y z ==> leq x z })
    , total :: (x:a -> y:a -> { leq x y || leq y x })
    }
@-}
data VerifiedOrd a = VerifiedOrd {
    leq :: a -> a -> Bool
  , refl :: a -> Proof
  , antisym :: a -> a -> Proof
  , trans :: a -> a -> a -> Proof
  , total :: a -> a -> Proof
  }
