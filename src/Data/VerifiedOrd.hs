{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE Trustworthy          #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-@ LIQUID "--higherorder"        @-}

module Data.VerifiedOrd where

import Data.Constraint                          ((:-) (..), Dict (..))
import Data.Reflection
import Data.VerifiableConstraint.Internal
import Data.VerifiedEq                          (VerifiedEq, eq)
import Language.Haskell.Liquid.ProofCombinators

{-@ data VerifiedOrd a = VerifiedOrd {
      leq :: (a -> a -> Bool)
    , reflo :: (x:a -> { leq x x })
    , antisym :: (x:a -> y:a -> { leq x y && leq y x ==> x == y })
    , transo :: (x:a -> y:a -> z:a -> { leq x y && leq y z ==> leq x z })
    , total :: (x:a -> y:a -> { leq x y || leq y x })
    , verifiedEq :: VerifiedEq a
    }
@-}

data VerifiedOrd a = VerifiedOrd {
    leq        :: a -> a -> Bool
  , reflo      :: a -> Proof
  , antisym    :: a -> a -> Proof
  , transo     :: a -> a -> a -> Proof
  , total      :: a -> a -> Proof
  , verifiedEq :: VerifiedEq a
  }

instance VerifiableConstraint Ord where
  newtype Verified Ord a = VOrd { vord :: VerifiedOrd a }
  reifiedIns = Sub Dict

instance Reifies s (Verified Ord a) => Eq (Lift Ord a s) where
  x == y = (eq . verifiedEq . vord . reflect $ x) (lower x) (lower y)

instance Reifies s (Verified Ord a) => Ord (Lift Ord a s) where
  x <= y = (leq . vord . reflect $ x) (lower x) (lower y)
