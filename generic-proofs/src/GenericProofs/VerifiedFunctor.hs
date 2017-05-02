{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exactdc"         @-}
{-# LANGUAGE RankNTypes #-}
module GenericProofs.VerifiedFunctor (VerifiedFunctor(..)) where

import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize _identity @-}
_identity :: a -> a
_identity x = x
{-# INLINE _identity #-}

{-@ axiomatize _compose @-}
_compose :: (b -> c) -> (a -> b) -> a -> c
_compose f g x = f (g x)
{-# INLINE _compose #-}

{-@
data VerifiedFunctor m = VerifiedFunctor {
    fmap        :: forall a b. (a -> b) -> m a -> m b
  , fmapId      :: forall a. x:m a -> { fmap _identity x == x }
  , fmapCompose :: forall a b c. f:(b -> c) -> g:(a -> b) -> x:m a
                -> { fmap (_compose f g) x == _compose (fmap f) (fmap g) x }
  }
@-}
data VerifiedFunctor m = VerifiedFunctor {
    fmap        :: forall a b. (a -> b) -> m a -> m b
  , fmapId      :: forall a. m a -> Proof
  , fmapCompose :: forall a b c. (b -> c) -> (a -> b) -> m a -> Proof
  }
