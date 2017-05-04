{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TypeOperators #-}

module GenericProofs.VerifiedEq.Examples.Sum where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.VerifiedEq
import GenericProofs.VerifiedEq.Generics
import GenericProofs.VerifiedEq.Instances

import Generics.Deriving.Newtypeless.Base.Internal

{-@ data MySum = MyLeft Int | MyRight Double @-}
data MySum = MyLeft Int | MyRight Double

type RepMySum = Sum (Rec0 Int) (Rec0 Double)

{-@ axiomatize fromMySum @-}
fromMySum :: MySum -> RepMySum x
fromMySum (MyLeft i)  = L1 (K1 i)
fromMySum (MyRight d) = R1 (K1 d)

{-@ axiomatize toMySum @-}
toMySum :: RepMySum x -> MySum
toMySum (L1 (K1 i)) = MyLeft i
toMySum (R1 (K1 d)) = MyRight d

{-@ tofMySum :: a:MySum
             -> { toMySum (fromMySum a) == a }
@-}
tofMySum :: MySum -> Proof
tofMySum a@(MyLeft i)
  =   toMySum (fromMySum a)
  -- ==. toMySum (fromMySum (MyLeft i))
  ==. toMySum (L1 (K1 i))
  ==. MyLeft i
  -- ==. a
  *** QED
tofMySum a@(MyRight d)
  =   toMySum (fromMySum a)
  -- ==. toMySum (fromMySum (MyRight d))
  ==. toMySum (R1 (K1 d))
  ==. MyRight d
  -- ==. a
  *** QED

{-@ fotMySum :: a:RepMySum x
             -> { fromMySum (toMySum a) == a }
@-}
fotMySum :: RepMySum x -> Proof
fotMySum a@(L1 (K1 i))
  =   fromMySum (toMySum a)
  -- ==. fromMySum (toMySum (L1 (K1 i)))
  ==. fromMySum (MyLeft i)
  -- ==. L1 (K1 i)
  -- ==. a
  *** QED
fotMySum a@(R1 (K1 d))
  =   fromMySum (toMySum a)
  -- ==. fromMySum (toMySum (R1 (K1 d)))
  ==. fromMySum (MyRight d)
  -- ==. R1 (K1 d)
  -- ==. a
  *** QED

isoMySum :: Iso (RepMySum x) MySum
isoMySum = Iso toMySum fromMySum tofMySum fotMySum

veqMySum :: VerifiedEq MySum
veqMySum = veqIso isoMySum $ veqSum (veqK1 veqInt) (veqK1 veqDouble)
