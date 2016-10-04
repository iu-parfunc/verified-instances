{-# LANGUAGE Trustworthy          #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies         #-}
{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--prune-unsorted"     @-}
{-@ LIQUID "--exactdc"            @-}

module Data.VerifiedEq where

-- import Data.Prod
import Data.Reflection
import Data.Constraint ((:-) (..), Dict (..))
import Data.VerifiableConstraint.Internal
import Language.Haskell.Liquid.ProofCombinators


{-@ data Prod a b = Prod { proj1 :: a , proj2 :: b } @-}
data Prod a b = Prod { proj1 :: a , proj2 :: b }

{-@ proj1Beta :: x:a -> y:b -> {proj1 (Prod x y) == x} @-}
proj1Beta :: a -> b -> Proof
proj1Beta x y = proj1 (Prod x y) ==. x *** QED 

{-@ proj2Beta :: x:a -> y:b -> {proj2 (Prod x y) == y} @-}
proj2Beta :: a -> b -> Proof
proj2Beta x y = proj2 (Prod x y) ==. y *** QED 

{-@ prodEta :: p:Prod a b -> {Prod (proj1 p) (proj2 p) == p} @-}
prodEta :: Prod a b -> Proof
prodEta p@(Prod _ _) = Prod (proj1 p) (proj2 p) ==. p *** QED 

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

{-@ eqProdRefl :: eqa:(a -> a -> Bool) -> eqaRefl:(x:a -> { Prop (eqa x x) })
               -> eqb:(b -> b -> Bool) -> eqbRefl:(y:b -> { Prop (eqb y y) })
               -> p:Prod a b 
               -> { eqProd eqa eqb p p }
@-}
eqProdRefl :: (a -> a -> Bool) -> (a -> Proof)
           -> (b -> b -> Bool) -> (b -> Proof)
           -> Prod a b -> Proof
eqProdRefl eqa eqaRefl eqb eqbRefl p@(Prod x y) =
      eqProd eqa eqb p p
  ==. (eqa (proj1 p) (proj1 p) && eqb (proj2 p) (proj2 p))
  ==. (eqa x x && eqb y y)
  ==. (True && eqb y y) ? eqaRefl x
  ==. (True && True)    ? eqbRefl y
  ==. True
  *** QED
