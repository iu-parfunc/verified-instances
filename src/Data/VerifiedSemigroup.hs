{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--prune-unsorted"  @-}

module Data.VerifiedSemigroup where

import Data.VerifiedEq
import Language.Haskell.Liquid.ProofCombinators

{-@ data VerifiedSemigroup a = VerifiedSemigroup {
      veq :: VerifiedEq a
    , op :: a -> a -> a
    , assoc :: x:a -> y:a -> z:a -> { v:() | veq.eq (op (op x y) z) (op x (op y z)) }
    }
@-}
data VerifiedSemigroup a = VerifiedSemigroup {
    veq :: VerifiedEq a
  , op :: a -> a -> a
  , assoc :: a -> a -> a -> Proof
}
