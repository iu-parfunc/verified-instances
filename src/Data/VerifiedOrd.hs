{-# LANGUAGE Trustworthy          #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies         #-}
{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}

module Data.VerifiedOrd (leqOrd) where

import Data.Constraint
import Data.Reflection
import Data.VerifiableConstraint.Internal
import Language.Haskell.Liquid.ProofCombinators

instance VerifiableConstraint Ord where
  data Verified Ord a = LEq (a -> a -> Bool)
                      | Cmp (a -> a -> Ordering)
  reifiedIns = Sub Dict

{-@
leqOrd :: leq:(a -> a -> Bool)
       -> total:(x:a -> y:a -> { Prop (leq x y) || Prop (leq y x) })
       -> antisym:(x:a -> y:a -> { Prop (leq x y) || Prop (leq y x) ==> x == y })
       -> trans:(x:a -> y:a -> z:a -> { Prop (leq x y) && Prop (leq y z) ==> Prop (leq x z) })
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
