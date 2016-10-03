{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--prune-unsorted"  @-}

module Fold where

import Data.Monoid
import Data.Traversable
import Data.VerifiedMonoid
import Data.VerifiedSemigroup
import Data.VerifiableConstraint
import Language.Haskell.Liquid.ProofCombinators

parFold :: Traversable t => VerifiedMonoid m -> (a -> m) -> t a -> m
parFold vmon f as = using (VMonoid vmon) $ foldMapDefault f as

{-@ newtype Prod = Prod { unProd :: Int } @-}
newtype Prod = Prod { unProd :: Int }
  deriving (Show, Eq, Ord)

{-@ axiomatize unProd @-}

{-@ assume unProdLInv :: x:Int -> { unProd (Prod x) == x } @-}
unProdLInv :: Int -> Proof
unProdLInv x = simpleProof

{-@ assume unProdRInv :: x:Prod -> { Prod (unProd x) == x } @-}
unProdRInv :: Prod -> Proof
unProdRInv x = simpleProof

{-@ axiomatize mult @-}
mult :: Prod -> Prod -> Prod
mult x y = Prod (unProd x * unProd y)

{-@ multAssoc :: x:Prod -> y:Prod -> z:Prod
              -> {mult x (mult y z) == mult (mult x y) z} @-}
multAssoc :: Prod -> Prod -> Prod -> Proof
multAssoc x y z =   mult x (mult y z)
                ==. Prod (unProd x * unProd (Prod (unProd y * unProd z)))
                ==. Prod (unProd x * (unProd y * unProd z)) ? unProdLInv (unProd y * unProd z)
                ==. Prod ((unProd x * unProd y) * unProd z)
                ==. Prod (unProd (Prod (unProd x * unProd y)) * unProd z) ? unProdLInv (unProd x * unProd y)
                ==. mult (mult x y) z
                *** QED

vSemigroupProd :: VerifiedSemigroup Prod
vSemigroupProd = VerifiedSemigroup mult multAssoc

{-@ axiomatize one @-}
{-@ one :: Prod @-}
one :: Prod
one = Prod 1

{-@ oneLident :: x:Prod -> {mult one x == x} @-}
oneLident :: Prod -> Proof
oneLident x =   mult one x
            ==. Prod (unProd (Prod 1) * unProd x)
            ==. Prod (1 * unProd x) ? unProdLInv 1
            ==. Prod (unProd x)
            ==. x ? unProdRInv x
            *** QED

{-@ oneRident :: x:Prod -> {mult x one == x} @-}
oneRident :: Prod -> Proof
oneRident x =   mult x one
            ==. Prod (unProd x * unProd (Prod 1))
            ==. Prod (unProd x * 1) ? unProdLInv 1
            ==. Prod (unProd x)
            ==. x ? unProdRInv x
            *** QED

vMonoidProd :: VerifiedMonoid Prod
vMonoidProd = VerifiedMonoid one vSemigroupProd oneLident oneRident

parFoldProd :: Traversable t => (a -> Prod) -> t a -> Prod
parFoldProd = parFold vMonoidProd
