{-@ LIQUID "--higherorder"        @-}

module IsoInt where

import Data.Iso
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize idInt @-}
idInt :: Int -> Int
idInt x = x

{-@ idoidInt :: x:Int -> {idInt (idInt x) == x} @-}
idoidInt :: Int -> Proof
idoidInt x = idInt (idInt x) ==. idInt x ==. x *** QED

isoIntInt :: Iso Int Int
isoIntInt = Iso idInt idInt idoidInt idoidInt

{-@ axiomatize sucInt @-}
sucInt :: Int -> Int
sucInt x = x + 1

{-@ axiomatize predInt @-}
predInt :: Int -> Int
predInt x = x - 1

{-@ sucopredInt :: x:Int -> {sucInt (predInt x) == x} @-}
sucopredInt :: Int -> Proof
sucopredInt x = sucInt (predInt x) ==. (x - 1) + 1 ==. x *** QED

{-@ predosucInt :: x:Int -> {predInt (sucInt x) == x} @-}
predosucInt :: Int -> Proof
predosucInt x = predInt (sucInt x) ==. (x + 1) - 1 ==. x *** QED

isoIntInt2 :: Iso Int Int
isoIntInt2 = Iso sucInt predInt sucopredInt predosucInt
