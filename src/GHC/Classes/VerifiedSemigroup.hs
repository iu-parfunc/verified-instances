{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--totality"    @-}

module GHC.Classes.VerifiedSemigroup where

import GHC.Classes.VerifiedEq
import Language.Haskell.Liquid.ProofCombinators

{-@ class (VerifiedEq a) => VerifiedSemigroup a where
      op :: a -> a -> a
      assoc :: x:a -> y:a -> z:a -> { v:() | eq (op (op x y) z) (op x (op y z)) }
@-}
class (VerifiedEq a) => VerifiedSemigroup a where
  op :: a -> a -> a
  assoc :: a -> a -> a -> Proof
