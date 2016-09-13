{-# LANGUAGE Trustworthy          #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies         #-}
{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}

module Data.VerifiedSemigroup (semigroup) where

import Data.Semigroup
import Data.Constraint
import Data.Reflection
import Data.VerifiableConstraint.Internal
import Language.Haskell.Liquid.ProofCombinators

instance VerifiableConstraint Semigroup where
  data Verified Semigroup a =
    VerifiedSemigroup { prod :: a -> a -> a }
  reifiedIns = Sub Dict

{-@
semigroup :: op:(a -> a -> a)
          -> assoc:(x:a -> y:a -> z:a -> {x `op` (y `op` z) == (x `op` y) `op` z})
          -> Verified Semigroup a
@-}
semigroup :: (a -> a -> a)
          -> (a -> a -> a -> Proof)
          -> Verified Semigroup a
semigroup op _ = VerifiedSemigroup op

instance Reifies s (Verified Semigroup a) => Semigroup (Lift Semigroup a s) where
  x <> y = Lift $ prod (reflect x) (lower x) (lower y)
