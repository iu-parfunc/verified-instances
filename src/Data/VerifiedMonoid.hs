{-# LANGUAGE Trustworthy          #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies         #-}
{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}

module Data.VerifiedMonoid (monoid) where

import Data.Monoid
import Data.Constraint
import Data.Reflection
import Data.VerifiableConstraint.Internal
import Language.Haskell.Liquid.ProofCombinators

instance VerifiableConstraint Monoid where
  data Verified Monoid a =
    VerifiedMonoid { vmempty :: a, vmappend :: a -> a -> a }
  reifiedIns = Sub Dict

{-@
monoid :: zero:a -> prod:(a -> a -> a)
       -> lident:(x:a -> {prod zero x == x})
       -> rident:(x:a -> {prod x zero == x})
       -> assoc:(x:a -> y:a -> z:a -> {prod x (prod y z) == prod (prod x y) z})
       -> Verified Monoid a
@-}
monoid :: a -> (a -> a -> a)
       -> (a -> Proof) -> (a -> Proof)
       -> (a -> a -> a -> Proof)
       -> Verified Monoid a
monoid zero prod _ _ _ = VerifiedMonoid zero prod

instance Reifies s (Verified Monoid a) => Monoid (Lift Monoid a s) where
  mempty = x where x = Lift $ vmempty (reflect x)
  x `mappend` y = Lift $ vmappend (reflect x) (lower x) (lower y)
