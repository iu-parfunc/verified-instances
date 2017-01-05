{-# LANGUAGE Trustworthy          #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies         #-}
{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}

module Data.VerifiedOrd where

import Data.Constraint
import Data.Reflection
import Data.VerifiedEq
import Data.VerifiableConstraint.Internal
import Language.Haskell.Liquid.ProofCombinators

{-@ data VerifiedOrd a = VerifiedOrd {
      leq :: (a -> a -> Bool)
    , refl :: (x:a -> { leq x x })
    , antisym :: (x:a -> y:a -> { leq x y && leq y x ==> x == y })
    , trans :: (x:a -> y:a -> z:a -> { leq x y && leq y z ==> leq x z })
    , total :: (x:a -> y:a -> { leq x y || leq y x })
    , verifiedEq :: VerifiedEq a
    }
@-}

data VerifiedOrd a = VerifiedOrd {
    leq :: a -> a -> Bool
  , refl :: a -> Proof
  , antisym :: a -> a -> Proof
  , trans :: a -> a -> a -> Proof
  , total :: a -> a -> Proof
  , verifiedEq :: VerifiedEq a
  }

instance VerifiableConstraint Ord where
  newtype Verified Ord a = VOrd { vord :: VerifiedOrd a }
  reifiedIns = Sub Dict

instance Reifies s (Verified Ord a) => Eq (Lift Ord a s) where
  x == y = (eq . verifiedEq . vord . reflect $ x) (lower x) (lower y)

instance Reifies s (Verified Ord a) => Ord (Lift Ord a s) where
  x <= y = (leq . vord . reflect $ x) (lower x) (lower y)
