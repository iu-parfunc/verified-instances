{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exactdc"         @-}
{-@ LIQUID "--prune-unsorted"  @-}
{-# LANGUAGE RankNTypes #-}
module GenericProofs.VerifiedFunctor (VerifiedFunctor(..)) where

import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize identity @-}
identity :: a -> a
identity x = x
{-# INLINE identity #-}

{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)
{-# INLINE compose #-}

{-@
data VerifiedFunctor m = VerifiedFunctor {
    fmap        :: forall a b. (a -> b) -> m a -> m b
  , fmapId      :: forall a. x:m a -> { fmap identity x == x }
  , fmapCompose :: forall a b c. f:(b -> c) -> g:(a -> b) -> x:m a
                -> { fmap (compose f g) x == compose (fmap f) (fmap g) x }
  }
@-}
data VerifiedFunctor m = VerifiedFunctor {
    fmap        :: forall a b. (a -> b) -> m a -> m b
  , fmapId      :: forall a. m a -> Proof
  , fmapCompose :: forall a b c. (b -> c) -> (a -> b) -> m a -> Proof
  }
