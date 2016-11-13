{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exactdc"         @-}
{-# LANGUAGE Rank2Types #-}

module Data.VerifiedMonad (VerifiedMonad(..)) where

import Language.Haskell.Liquid.ProofCombinators

{-@
data VerifiedMonad m = VerifiedMonad {
    return       :: forall a. a -> m a
  , bind         :: forall a b. m a -> (a -> m b) -> m b
  , returnLIdent :: forall a b. x:a -> f:(a -> m b) -> { bind (return x) f == f x }
  , returnRIdent :: forall a. f:m a -> { bind f return == f }
  , bindAssoc    :: forall a b c. f:m a -> g:(a -> m b) -> h:(b -> m c)
                 -> { bind (bind f g) h == bind f (\x:a -> bind (g x) h) }
}
@-}
data VerifiedMonad m = VerifiedMonad {
    return       :: forall a. a -> m a
  , bind         :: forall a b. m a -> (a -> m b) -> m b
  , returnLIdent :: forall a b. a -> (a -> m b) -> Proof
  , returnRIdent :: forall a. m a -> Proof
  , bindAssoc    :: forall a b c. m a -> (a -> m b) -> (b -> m c) -> Proof
}
