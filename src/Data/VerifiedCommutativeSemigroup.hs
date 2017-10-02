{-# LANGUAGE Trustworthy          #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies         #-}
{-@ LIQUID "--higherorder"        @-}

module Data.VerifiedCommutativeSemigroup where

import Data.CommutativeSemigroup
import Data.Constraint
import Data.Reflection
import Data.Semigroup
import Data.VerifiableConstraint.Internal
import Data.VerifiedSemigroup
import Language.Haskell.Liquid.ProofCombinators

-- {-@ data VerifiedCommutativeSemigroup a = VerifiedCommutativeSemigroup {
--       commutes :: x:a -> y:a
--                -> { prod verifiedSemigroup x y == prod verifiedSemigroup y x }
--     , verifiedSemigroup :: VerifiedSemigroup a
--     }
-- @-}
data VerifiedCommutativeSemigroup a = VerifiedCommutativeSemigroup {
    commutes :: a -> a -> Proof
  , verifiedSemigroup :: VerifiedSemigroup a
  }

{-@ VerifiedCommutativeSemigroup ::
        commutes: (x:a
                   -> y:a
                   -> { prod verifiedSemigroup x y == prod verifiedSemigroup y x })
     -> verifiedSemigroup: VerifiedSemigroup a
     -> VerifiedCommutativeSemigroup a
@-}

instance VerifiableConstraint CommutativeSemigroup where
  newtype Verified CommutativeSemigroup a = VCommutativeSemigroup
    { vCommutativeSemigroup :: VerifiedCommutativeSemigroup a }
  reifiedIns = Sub Dict

instance Reifies s (Verified CommutativeSemigroup a)
    => Semigroup (Lift CommutativeSemigroup a s) where
  x <> y = Lift $ (prod . verifiedSemigroup . vCommutativeSemigroup . reflect $ x)
                  (lower x) (lower y)

instance Reifies s (Verified CommutativeSemigroup a)
    => CommutativeSemigroup (Lift CommutativeSemigroup a s)
