{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE Trustworthy          #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--prune-unsorted"     @-}
{-@ LIQUID "--exactdc"            @-}

module Data.VerifiedEq where

import Data.Constraint                          ((:-) (..), Dict (..))
import Data.Reflection
import Data.VerifiableConstraint.Internal
import Language.Haskell.Liquid.ProofCombinators

{-@ data VerifiedEq a = VerifiedEq {
      eq :: a -> a -> Bool
    , refl :: x:a -> { v:() | eq x x }
    , sym :: x:a -> y:a -> { v:() | eq x y ==> eq y x }
    , trans :: x:a -> y:a -> z:a -> { v:() | eq x y && eq y z ==> eq x z }
    }
@-}

data VerifiedEq a = VerifiedEq {
    eq    :: a -> a -> Bool
  , refl  :: a -> Proof
  , sym   :: a -> a -> Proof
  , trans :: a -> a -> a -> Proof
  }

instance VerifiableConstraint Eq where
  newtype Verified Eq a = VEq { veq :: VerifiedEq a }
  reifiedIns = Sub Dict

instance Reifies s (Verified Eq a) => Eq (Lift Eq a s) where
  x == y = (eq . veq . reflect $ x) (lower x) (lower y)
