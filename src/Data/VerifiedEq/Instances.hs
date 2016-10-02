{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--prune-unsorted"  @-}

module Data.VerifiedEq.Instances where

import Data.VerifiedEq
import Language.Haskell.Liquid.ProofCombinators

{-@ eqIntRefl :: x:Int -> { x == x } @-}
eqIntRefl :: Int -> Proof
eqIntRefl _ = simpleProof

{-@ eqIntSym :: x:Int -> y:Int -> { x == y ==> y == x } @-}
eqIntSym :: Int -> Int -> Proof
eqIntSym _ _ = simpleProof

{-@ eqIntTrans :: x:Int -> y:Int -> z:Int -> { x == y && y == z ==> x == z } @-}
eqIntTrans :: Int -> Int -> Int -> Proof
eqIntTrans _ _ _ = simpleProof

-- veqInt :: VerifiedEq Int
-- veqInt = VerifiedEq (==) eqIntRefl eqIntSym eqIntTrans
