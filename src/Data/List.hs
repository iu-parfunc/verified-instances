{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorderqs"   @-}
{-@ LIQUID "--prune-unsorted"  @-}

module Data.List where

import Language.Haskell.Liquid.ProofCombinators

{-@ data List [llen] = Nil | Cons { x :: a , xs :: List a } @-}
data List a = Nil | Cons a (List a)

{-@ measure llen @-}
{-@ llen :: List a -> Nat @-}
llen :: List a -> Int
llen Nil = 0
llen (Cons x xs) = 1 + llen xs

{-@ axiomatize appendList @-}
appendList :: List a -> List a -> List a
appendList Nil ys = ys
appendList (Cons x xs) ys = Cons x (appendList xs ys)

{-@ axiomatize eqList @-}
eqList :: Eq a => List a -> List a -> Bool
eqList Nil Nil = True
eqList (Cons x xs) (Cons y ys) = if x == y then eqList xs ys else False
eqList _ _ = False

{-@ eqListRefl :: xs:List a -> {v:() | eqList xs xs} @-}
eqListRefl :: Eq a => List a -> Proof
eqListRefl Nil = undefined
-- eqListRefl Nil =   eqList Nil Nil
--                ==. True
--                *** QED
eqListRefl (Cons x xs) =   eqList (Cons x xs) (Cons x xs)
                       ==. (if x == x then eqList xs xs else False)
                       ==. eqList xs xs
                       ==. True ? eqListRefl xs
                       *** QED

{-@ eqListSym :: xs:List a -> ys: List a -> {v:() | eqList xs ys ==> eqList ys xs} @-}
eqListSym :: Eq a => List a -> List a -> Proof
eqListSym Nil Nil = simpleProof
eqListSym Nil (Cons y ys) =   eqList Nil (Cons y ys)
                          ==. False
                          *** QED
eqListSym (Cons x xs) Nil =   eqList (Cons x xs) Nil
                          ==. False
                          *** QED
eqListSym (Cons x xs) (Cons y ys) =   eqList (Cons x xs) (Cons y ys)
                                  ==. (if x == y then eqList xs ys else False)
                                  ==. (if y == x then eqList xs ys else False)
                                  ==. (if y == x then eqList ys xs else False) ? eqListSym xs ys
                                  ==. eqList (Cons y ys) (Cons x xs)
                                  ==. eqList ys xs
                                  *** QED
