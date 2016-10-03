{-# LANGUAGE Trustworthy          #-}
{-@ LIQUID "--totality"           @-}

module Data.Prod where

import Language.Haskell.Liquid.ProofCombinators

{-@ data Prod a b = Prod { proj1 :: a , proj2 :: b } @-}
data Prod a b = Prod { proj1 :: a , proj2 :: b }

{-@ assume proj1Beta :: x:a -> y:b -> {proj1 (Prod x y) == x} @-}
proj1Beta :: a -> b -> Proof
proj1Beta x y = undefined

{-@ assume proj2Beta :: x:a -> y:b -> {proj2 (Prod x y) == y} @-}
proj2Beta :: a -> b -> Proof
proj2Beta x y = undefined

{-@ assume prodEta :: p:Prod a b -> {Prod (proj1 p) (proj2 p) == p} @-}
prodEta :: Prod a b -> Proof
prodEta p = undefined
