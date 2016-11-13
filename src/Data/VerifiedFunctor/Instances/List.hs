{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exactdc"         @-}

module Data.VerifiedFunctor.Instances.List where

import Data.VerifiedFunctor
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize identity @-}
identity :: a -> a
identity x = x

{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{-@ data List [lengthList] = Nil | Cons { x :: a, xs :: List a } @-}
data List a = Nil | Cons a (List a)

{-@ measure lengthList @-}
{-@ lengthList :: List a -> Nat @-}
lengthList :: List a -> Int
lengthList Nil         = 0
lengthList (Cons x xs) = 1 + lengthList xs

{-@ axiomatize mapList @-}
mapList :: (a -> b) -> List a -> List b
mapList f Nil         = Nil
mapList f (Cons x xs) = Cons (f x) (mapList f xs)

{-@ mapListId :: x:List a -> { mapList identity x == x } @-}
mapListId :: List a -> Proof
mapListId Nil = mapList identity Nil ==. Nil *** QED
mapListId (Cons x xs) = mapList identity (Cons x xs)
                    ==. Cons (identity x) (mapList identity xs)
                    ==. Cons x (mapList identity xs)
                    ==. Cons x xs ? mapListId xs
                    *** QED

{-@ mapListCompose :: f:(b -> c) -> g:(a -> b) -> x:List a
                   -> { mapList (compose f g) x == compose (mapList f) (mapList g) x }
@-}
mapListCompose :: (b -> c) -> (a -> b) -> List a -> Proof
mapListCompose f g Nil = mapList (compose f g) Nil
                     ==. Nil
                     ==. (mapList f) (mapList g Nil)
                     ==. compose (mapList f) (mapList g) Nil
                     *** QED
mapListCompose f g (Cons x xs) = mapList (compose f g) (Cons x xs)
                             ==. Cons (compose f g x) (mapList (compose f g) xs)
                             ==. Cons (compose f g x) (compose (mapList f) (mapList g) xs) ? mapListCompose f g xs
                             ==. Cons (f (g x)) (mapList f (mapList g xs))
                             ==. mapList f (Cons (g x) (mapList g xs))
                             ==. mapList f (mapList g (Cons x xs))
                             ==. compose (mapList f) (mapList g) (Cons x xs)
                             *** QED

vFunctorList :: VerifiedFunctor List
vFunctorList = VerifiedFunctor mapList mapListId mapListCompose
