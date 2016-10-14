{-# LANGUAGE Trustworthy #-}

module Data.CommutativeSemigroup where

import Data.Semigroup

-- | Like 'Semigroup', but with the additional stipulation that '<>' be
-- commutative.
class Semigroup a => CommutativeSemigroup a where
