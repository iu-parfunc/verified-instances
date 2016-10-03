{-# LANGUAGE Trustworthy          #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies         #-}
{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}

module Data.VerifiedEq where

import Data.Constraint
import Data.Reflection
import Data.VerifiableConstraint.Internal
import Language.Haskell.Liquid.ProofCombinators

{-@ data VerifiedEq a = VerifiedEq {
      eq :: a -> a -> Bool
    , refl :: x:a -> { v:() | Prop (eq x x) }
    , sym :: x:a -> y:a -> { v:() | Prop (eq x y) ==> Prop (eq y x) }
    , trans :: x:a -> y:a -> z:a -> { v:() | Prop (eq x y) && Prop (eq y z) ==> Prop (eq x z) }
    }
@-}
data VerifiedEq a = VerifiedEq {
    eq :: a -> a -> Bool
  , refl :: a -> Proof
  , sym :: a -> a -> Proof
  , trans :: a -> a -> a -> Proof
  }

instance VerifiableConstraint Eq where
  data Verified Eq a = Verified { veq :: VerifiedEq a }
  reifiedIns = Sub Dict

instance Reifies s (Verified Eq a) => Eq (Lift Eq a s) where
  x == y = eq (veq $ reflect x) (lower x) (lower y)
