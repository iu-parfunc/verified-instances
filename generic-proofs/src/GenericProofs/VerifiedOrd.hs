{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
module GenericProofs.VerifiedOrd (VerifiedOrd(..), {-vordEq,-} eqCompare) where

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

{-
-- | Test for equality using 'VerifiedOrd'.
{-@ axiomatize vordEq @-}
vordEq :: VerifiedOrd a -> a -> a -> Bool
vordEq (VerifiedOrd { leq = leq' }) = eqCompare leq'
{-# INLINE vordEq #-}
-}

-- | Test for equality using a 'leq' function.
{-@ axiomatize eqCompare @-}
eqCompare :: (a -> a -> Bool) -> a -> a -> Bool
eqCompare cmp x y = cmp x y && cmp y x
{-# INLINE eqCompare #-}
