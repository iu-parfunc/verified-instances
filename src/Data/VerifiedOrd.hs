{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies         #-}
{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}

module Data.VerifiedOrd (leqOrd) where

import Language.Haskell.Liquid.ProofCombinators
import Data.VerifiableConstraint
import Data.Proxy
import Data.Reflection
import Data.Constraint
import Data.Constraint.Unsafe

instance VerifiableConstraint Ord where
  data Verified Ord a = LEq (a -> a -> Bool)
                      | Cmp (a -> a -> Ordering)
  reifiedIns = Sub Dict

{-@
leqOrd :: leq:(a -> a -> Bool)
       -> (x:a -> y:a -> { v:() | Prop (leq x y) || Prop (leq y x) })
       -> (x:a -> y:a -> { v:() | Prop (leq x y) || Prop (leq y x) ==> x == y })
       -> (x:a -> y:a -> z:a -> { v:() | Prop (leq x y) && Prop (leq y z) ==> Prop (leq x z) })
       -> Verified Ord a
 @-}
leqOrd :: (a -> a -> Bool)
       -> (a -> a -> Proof)
       -> (a -> a -> Proof)
       -> (a -> a -> a -> Proof)
       -> Verified Ord a
leqOrd leq total antisym trans = LEq leq

instance Reifies s (Verified Ord a) => Eq (Lift Ord a s) where
  a == b = (compare a b == EQ)

instance Reifies s (Verified Ord a) => Ord (Lift Ord a s) where
  compare x y =
    case reflect x of
      LEq f -> if (x == y)
                 then EQ
                 else if f (lower x) (lower y)
                        then LT
                        else GT
      Cmp f -> f (lower x) (lower y)
