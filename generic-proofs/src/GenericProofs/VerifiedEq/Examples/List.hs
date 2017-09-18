{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
module GenericProofs.VerifiedEq.Examples.List where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedEq
import GenericProofs.VerifiedEq.Generics

import Generics.Deriving.Newtypeless.Base.Internal

{-@ data List [listLength] a = Nil | Cons { x :: a , xs :: List a } @-}
data List a = Nil | Cons a (List a)

{-@ measure listLength @-}
{-@ listLength :: List a -> Nat @-}
listLength :: List a -> Int
listLength Nil         = 0
listLength (Cons _ xs) = 1 + listLength xs

{-
type RepList a = D1 D1List (C1 C1_0List U1 `Sum` C1 C1_1List
                              (S1 NoSelector (Rec0 a) `Product`
                               S1 NoSelector (Rec0 (List a))))

data D1List
data C1_0List
data C1_1List
data S1_1_0List
data S1_1_1List

{-@ axiomatize fromList @-}
fromList :: List a -> RepList a x
fromList Nil = M1 (L1 (M1 U1))
fromList (Cons x xs) = M1 (R1 (M1 (Product (M1 (K1 x)) (M1 (K1 xs)))))

{-@ axiomatize toList @-}
toList :: RepList a x -> List a
toList (M1 (L1 (M1 U1))) = Nil
toList (M1 (R1 (M1 (Product (M1 (K1 x)) (M1 (K1 xs)))))) = Cons x xs

{-@ tofList :: l:List a
            -> { toList (fromList l) == l }
@-}
tofList :: List a -> Proof
tofList l@Nil
  =   toList (fromList l)
  ==. toList (M1 (L1 (M1 U1)))
  ==. l
  *** QED
tofList l@(Cons x xs)
  =   toList (fromList l)
  ==. toList (M1 (R1 (M1 (Product (M1 (K1 x)) (M1 (K1 xs))))))
  ==. l
  *** QED

{-@ fotList :: r:RepList a x
            -> { fromList (toList r) == r }
@-}
fotList :: RepList a x -> Proof
fotList r@(M1 (L1 (M1 U1)))
  =   fromList (toList r)
  ==. fromList Nil
  ==. r
  *** QED
fotList r@(M1 (R1 (M1 (Product (M1 (K1 x)) (M1 (K1 xs))))))
  =   fromList (toList r)
  ==. fromList (Cons x xs)
  ==. r
  *** QED

isoList :: Iso (List a) (RepList a x)
isoList = Iso fromList toList fotList tofList
-}

{-@ axiomatize fromList @-}
{-@ axiomatize toList @-}
{-@ tofList :: l:List a
            -> { toList (fromList l) == l }
@-}
{-@ fotList :: r:RepList a x
            -> { fromList (toList r) == r }
@-}
$(deriveIso "RepList"
            "toList" "fromList"
            "tofList" "fotList"
            "isoList"
            ''List)

{-@ lazy veqList @-}
veqList :: VerifiedEq a -> VerifiedEq (List a)
veqList veqA
  = veqContra fromList $ veqM1
                       $ veqSum (veqM1 veqU1)
                                (veqM1 $ veqProd (veqM1 $ veqK1 veqA)
                                                 (veqM1 $ veqK1 $ veqList veqA))
