{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exactdc"         @-}
{-# LANGUAGE Rank2Types #-}

module Data.VerifiedFunctor (VerifiedFunctor(..)) where

import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize identity @-}
identity :: a -> a
identity x = x

{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{-@
data VerifiedFunctor m = VerifiedFunctor {
    map        :: forall a b. (a -> b) -> m a -> m b
  , mapId      :: forall a. x:m a -> { map identity x == x }
  , mapCompose :: forall a b c. f:(b -> c) -> g:(a -> b) -> x:m a
               -> { map (compose f g) x == compose (map f) (map g) x }
}
@-}
data VerifiedFunctor m = VerifiedFunctor {
    map        :: forall a b. (a -> b) -> m a -> m b
  , mapId      :: forall a. m a -> Proof
  , mapCompose :: forall a b c. (b -> c) -> (a -> b) -> m a -> Proof
}
