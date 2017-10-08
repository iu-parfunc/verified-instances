{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--noadt"              @-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedFunctor.Examples.List where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedFunctor
import GenericProofs.VerifiedFunctor.Generics

import Generics.Deriving.Newtypeless.Base.Internal

{-@ data List a = Nil | Cons { hd :: a, tl :: List a } @-}
data List a = Nil | Cons { hd :: a, tl :: List a }

{-
type RepList = Sum U1 (Product Par1 (Rec1 List))

{-@ axiomatize fromList @-}
fromList :: forall a. List a -> RepList a
fromList Nil         = L1 U1
fromList (Cons x xs) = R1 (Product (Par1 x) (Rec1 xs))

{-@ axiomatize toList @-}
toList :: forall a. RepList a -> List a
toList (L1 U1)                           = Nil
toList (R1 (Product (Par1 x) (Rec1 xs))) = Cons x xs

{-@ tofList :: forall a. l:List a -> { toList (fromList l) == l } @-}
tofList :: forall a. List a -> Proof
tofList Nil
  =   toList (fromList Nil)
  ==. toList (L1 U1)
  ==. Nil
  *** QED
tofList (Cons x xs)
  =   toList (fromList (Cons x xs))
  ==. toList (R1 (Product (Par1 x) (Rec1 xs)))
  ==. Cons x xs
  *** QED

{-@ fotList :: forall a. l:RepList a -> { fromList (toList l) == l } @-}
fotList :: forall a. RepList a -> Proof
fotList (L1 U1)
  =   fromList (toList (L1 U1))
  ==. fromList Nil
  ==. L1 U1
  *** QED
fotList (R1 (Product (Par1 x) (Rec1 xs)))
  =   fromList (toList (R1 (Product (Par1 x) (Rec1 xs))))
  ==. fromList (Cons x xs)
  ==. R1 (Product (Par1 x) (Rec1 xs))
  *** QED
-}

{-@ axiomatize fromList @-}
{-@ axiomatize toList @-}
{-@ tofList :: forall a. l:List a -> { toList (fromList l) == l } @-}
{-@ fotList :: forall a. l:RepList a -> { fromList (toList l) == l } @-}
$(deriveIso1 "RepList"
             "toList" "fromList"
             "tofList" "fotList"
             "isoList"
             ''List)

{-
isoList :: Iso1 RepList List
isoList = Iso1 toList fromList tofList fotList
-}

{-@ lazy vfunctorList @-}
vfunctorList :: VerifiedFunctor List
vfunctorList = vfunctorIso (iso1Sym isoList)
             $ vfunctorM1
             $ vfunctorSum (vfunctorM1 vfunctorU1)
                           (vfunctorM1 $ vfunctorProduct (vfunctorM1 vfunctorPar1)
                                                         (vfunctorM1 $ vfunctorRec1 vfunctorList))
