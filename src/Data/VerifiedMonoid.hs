{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Trustworthy           #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}

module Data.VerifiedMonoid where

import Data.Constraint
import Data.Reflection
import Data.Semigroup
import Data.VerifiableConstraint.Internal
import Language.Haskell.Liquid.ProofCombinators

{-@ data VerifiedMonoid a = VerifiedMonoid {
      ident  :: a
    , prod   :: a -> a -> a
    , lident :: x:a -> { prod ident x == x }
    , rident :: x:a -> { prod x ident == x }
    , assoc  :: x:a -> y:a -> z:a
             -> { prod x (prod y z) == prod (prod x y) z }
    }
@-}

data VerifiedMonoid a = VerifiedMonoid {
    ident  :: a
  , prod   :: a -> a -> a
  , lident :: a -> Proof
  , rident :: a -> Proof
  , assoc  :: a -> a -> a -> Proof
}

instance VerifiableConstraint Monoid where
  newtype Verified Monoid a = VMonoid { vmonoid :: VerifiedMonoid a }
  reifiedIns = Sub Dict

instance Reifies s (Verified Monoid a) => Semigroup (Lift Monoid a s) where
  x <> y = Lift $ (prod . vmonoid . reflect $ x) (lower x) (lower y)

instance Reifies s (Verified Monoid a) => Monoid (Lift Monoid a s) where
  mempty = x where x = Lift . ident . vmonoid . reflect $ x
  x `mappend` y = Lift $ (prod . vmonoid . reflect $ x) (lower x) (lower y)
