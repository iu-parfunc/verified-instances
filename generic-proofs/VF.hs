-- VF.hs
{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exactdc"         @-}
{-# LANGUAGE RankNTypes #-}
module VF (VerifiedFunctor(..)) where

import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize _identity @-}
_identity :: a -> a
_identity x = x
{-# INLINE _identity #-}

{-@
data VerifiedFunctor m = VerifiedFunctor {
    fmap   :: forall a b. (a -> b) -> m a -> m b
  , fmapId :: forall a. x:m a -> { fmap _identity x == x }
  }
@-}
data VerifiedFunctor m = VerifiedFunctor {
    fmap   :: forall a b. (a -> b) -> m a -> m b
  , fmapId :: forall a. m a -> Proof
  }
