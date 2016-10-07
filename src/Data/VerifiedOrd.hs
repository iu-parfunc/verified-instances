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
    , total :: (x:a -> y:a -> { Prop (leq x y) || Prop (leq y x) })
    , antisym :: (x:a -> y:a -> { Prop (leq x y) || Prop (leq y x) ==> x == y })
    , trans :: (x:a -> y:a -> z:a -> { Prop (leq x y) && Prop (leq y z) ==> Prop (leq x z) })
    , verifiedEq :: VerifiedEq a
    }
@-}

data VerifiedOrd a = VerifiedOrd {
    leq :: a -> a -> Bool
  , total :: a -> a -> Proof
  , antisym :: a -> a -> Proof
  , trans :: a -> a -> a -> Proof
  , verifiedEq :: VerifiedEq a
  }

instance VerifiableConstraint Ord where
  newtype Verified Ord a = VOrd { vord :: VerifiedOrd a }
  reifiedIns = Sub Dict

instance Reifies s (Verified Ord a) => Eq (Lift Ord a s) where
  x == y = (eq . verifiedEq . vord . reflect $ x) (lower x) (lower y)

instance Reifies s (Verified Ord a) => Ord (Lift Ord a s) where
  x <= y = (leq . vord . reflect $ x) (lower x) (lower y)
