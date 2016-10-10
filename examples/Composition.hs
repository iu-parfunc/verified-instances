{-@ LIQUID "--totality"    @-}
{-@ LIQUID "--higherorder" @-}

module Composition where

import Data.VerifiedEq
import Data.VerifiableConstraint

{-@ assume veqInt :: VerifiedEq Int @-}
veqInt :: VerifiedEq Int
veqInt = VerifiedEq (==) undefined undefined undefined

{-@ assume veqString :: VerifiedEq String @-}
veqString :: VerifiedEq String
veqString = VerifiedEq (==) undefined undefined undefined

-- This is a bad thing
x :: Bool
x = using (VEq veqInt)
  $ using (VEq veqString)
  $ ('1', "foo") /= ('2', "bar")

y :: Bool
y = using (VEq veqInt)
  $ using (VEq veqString)
  $ Left '1' /= Right "foo"
