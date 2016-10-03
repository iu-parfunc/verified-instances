{-# LANGUAGE Trustworthy          #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies         #-}
{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--prune-unsorted"     @-}

module Data.VerifiedEq where

import Data.Prod
import Data.Reflection
import Data.Constraint ((:-) (..), Dict (..))
import Data.VerifiableConstraint.Internal
import Language.Haskell.Liquid.ProofCombinators

{-@ data VerifiedEq a = VerifiedEq {
      eq :: a -> a -> Bool
    , refl :: x:a -> { v:() | Prop (eq x x) }
    , sym :: x:a -> y:a -> { v:() | Prop (eq x y) ==> Prop (eq y x) }
    , trans :: x:a -> y:a -> z:a -> { v:() | Prop (eq x y) && Prop (eq y z) ==> Prop (eq x z) }
    }
@-}
data VerifiedEq a = VerifiedEq {
    eq :: a -> a -> Bool
  , refl :: a -> Proof
  , sym :: a -> a -> Proof
  , trans :: a -> a -> a -> Proof
  }

instance VerifiableConstraint Eq where
  data Verified Eq a = VEq { veq :: VerifiedEq a }
  reifiedIns = Sub Dict

instance Reifies s (Verified Eq a) => Eq (Lift Eq a s) where
  x == y = (eq . veq . reflect $ x) (lower x) (lower y)

{-@ axiomatize eqProd @-}
{-@ eqProd :: (a -> a -> Bool) -> (b -> b -> Bool)
           -> Prod a b -> Prod a b -> Bool @-}
eqProd :: (a -> a -> Bool) -> (b -> b -> Bool)
       -> Prod a b -> Prod a b -> Bool
eqProd eqa eqb p q =
  eqa (proj1 p) (proj1 q) && eqb (proj2 p) (proj2 q)

{-@ eqProdRefl :: eqa:(a -> a -> Bool) -> eqaRefl:(x:a -> {Prop (eqa x x)})
               -> eqb:(b -> b -> Bool) -> eqbRefl:(y:b -> {Prop (eqb y y)})
               -> p:Prod a b -> { eqProd eqa eqb p p }
@-}
eqProdRefl :: (a -> a -> Bool) -> (a -> Proof)
           -> (b -> b -> Bool) -> (b -> Proof)
           -> Prod a b -> Proof
eqProdRefl eqa eqaRefl eqb eqbRefl (Prod x y) =
      eqProd eqa eqb (Prod x y) (Prod x y)
  ==. (eqa x x && eqb y y)
  ==. (True && eqb y y) ? eqaRefl x
  ==. (True && True) ? eqbRefl y
  ==. True
  *** QED
