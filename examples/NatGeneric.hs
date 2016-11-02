{-@ LIQUID "--totality"       @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--no-termination" @-}

module Main where

import Data.Iso
import Data.VerifiableConstraint
import Data.VerifiedEq
import Data.VerifiedEq.Instances
import Language.Haskell.Liquid.ProofCombinators

data Nat = Zero | Succ Nat

type NatRep = Either () Nat

fromRep :: NatRep -> Nat
fromRep (Left ()) = Zero
fromRep (Right x) = x

toRep :: Nat -> NatRep
toRep Zero     = Left ()
toRep (Succ n) = Right n

veqNatRep :: VerifiedEq NatRep
veqNatRep = veqSum veqUnit veqNat

veqNat :: VerifiedEq Nat
veqNat = veqContra toRep veqNatRep

main :: IO ()
main = print $ using (VEq veqNat) $
  Succ (Succ (Succ Zero)) == Succ (Succ (Succ (Succ Zero)))
