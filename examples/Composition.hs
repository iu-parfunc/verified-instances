{-@ LIQUID "--totality"    @-}
{-@ LIQUID "--exactdc"     @-}
{-@ LIQUID "--higherorder" @-}

module Composition where

import Data.VerifiedEq
import Data.VerifiedEq.Instances
import Data.VerifiableConstraint
import Language.Haskell.Liquid.ProofCombinators

{-@ assume veqString :: VerifiedEq String @-}
veqString :: VerifiedEq String
veqString = VerifiedEq (==) undefined undefined undefined

-- bad usage
x :: Bool
x = using (VEq veqInt)
  $ using (VEq veqString)
  $ ('1', "foo") /= ('2', "bar")

y :: Bool
y = using (VEq veqInt)
  $ using (VEq veqString)
  $ Left '1' /= Right "foo"

-- good usage
x' :: Bool
x' = using (VEq $ veqProd veqInt veqString)
   $ ('1', "foo") /= ('2', "bar")

y' :: Bool
y' = using (VEq $ veqSum veqInt veqString)
   $ Left '1' /= Right "foo"
