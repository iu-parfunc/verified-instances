{-# LANGUAGE Trustworthy          #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies         #-}
{-@ LIQUID "--higherorder"        @-}

module Data.VerifiedSemigroup where

import Data.Semigroup
import Data.Constraint
import Data.Reflection
import Data.VerifiableConstraint.Internal
import Language.Haskell.Liquid.ProofCombinators

{-@ data VerifiedSemigroup a = VerifiedSemigroup {
      prod :: a -> a -> a
    , assoc :: x:a -> y:a -> z:a
            -> { prod x (prod y z) == prod (prod x y) z }
    }
@-}
data VerifiedSemigroup a = VerifiedSemigroup {
    prod :: a -> a -> a
  , assoc :: a -> a -> a -> Proof
  }

instance VerifiableConstraint Semigroup where
  newtype Verified Semigroup a = VSemigroup { vsemigroup :: VerifiedSemigroup a }
  reifiedIns = Sub Dict

instance Reifies s (Verified Semigroup a) => Semigroup (Lift Semigroup a s) where
  x <> y = Lift $ (prod . vsemigroup . reflect $ x) (lower x) (lower y)
