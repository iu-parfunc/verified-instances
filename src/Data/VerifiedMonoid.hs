{-# LANGUAGE Trustworthy          #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies         #-}
{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}

module Data.VerifiedMonoid where

import Data.Monoid
import Data.Semigroup
import Data.Constraint
import Data.Reflection
import Data.VerifiedSemigroup
import Data.VerifiableConstraint.Internal
import Language.Haskell.Liquid.ProofCombinators

-- {-@ data VerifiedMonoid a = VerifiedMonoid {
--       ident :: a
--     , verifiedSemigroup :: VerifiedSemigroup a
--     , lident :: x:a -> {prod verifiedSemigroup ident x == x}
--     , rident :: x:a -> {prod verifiedSemigroup x ident == x}
--     }
-- @-}

data VerifiedMonoid a = VerifiedMonoid {
    ident :: a
  , verifiedSemigroup :: VerifiedSemigroup a
  , lident :: a -> Proof
  , rident :: a -> Proof
}

{-@ VerifiedMonoid :: ident: a
                   -> verifiedSemigroup: VerifiedSemigroup a
                   -> lident: (x:a -> {prod verifiedSemigroup ident x == x})
                   -> rident: (x:a -> {prod verifiedSemigroup x ident == x})
                   -> VerifiedMonoid a
@-}

instance VerifiableConstraint Monoid where
  newtype Verified Monoid a = VMonoid { vmonoid :: VerifiedMonoid a }
  reifiedIns = Sub Dict

instance Reifies s (Verified Monoid a) => Semigroup (Lift Monoid a s) where
  x <> y = Lift $ (prod . verifiedSemigroup . vmonoid . reflect $ x) (lower x) (lower y)

instance Reifies s (Verified Monoid a) => Monoid (Lift Monoid a s) where
  mempty = x where x = Lift . ident . vmonoid . reflect $ x
  x `mappend` y = Lift $ (prod . verifiedSemigroup . vmonoid . reflect $ x) (lower x) (lower y)
