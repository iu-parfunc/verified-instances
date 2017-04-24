{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TypeOperators #-}

module GenericProofs.VerifiedEq.Examples.Sum where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.VerifiedEq
-- import GenericProofs.VerifiedEq.Generics        (veqK1, veqSum)
import GenericProofs.VerifiedEq.Instances

import Generics.Deriving.Newtypeless

{-@ data MySum = MyLeft Int | MyRight Double @-}
data MySum = MyLeft Int | MyRight Double

-- | Begin manual reflection of imported data types:

{- data K1 i c p = K1 { unK1 :: c } -}

{-@ assume K1   :: c:c -> {v:K1 i c p | v == K1 c &&  unK1 v == c && select_K1_1 v == c } @-}
{-@ assume unK1 :: k:K1 i c p -> {v:c | v == unK1 k && v == select_K1_1 k && K1 v == k} @-}

{-@ measure select_K1_1 :: K1 i c p -> c @-}
{-@ measure unK1        :: K1 i c p -> c @-}

{- data Sum f g p = L1 (f p) | R1 (g p) -}

{-@ assume L1 :: a:(f p)
              -> {v:Sum f g p | v == L1 a && select_L1_1 v == a && is_L1 v && not (is_R1 v)} @-}
{-@ assume R1 :: b:(g p)
              -> {v:Sum f g p | v == R1 b && select_R1_1 v == b && not (is_L1 v) && is_R1 v } @-}

{-@ measure select_L1_1 :: Sum f g p -> f p @-}
{-@ measure select_R1_1 :: Sum f g p -> g p @-}
{-@ measure is_L1 :: Sum f g p -> Bool @-}
{-@ measure is_R1 :: Sum f g p -> Bool @-}

-- | END manual reflection of imported data types

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
  ==. toMySum (fromMySum (MyLeft i))
  ==. toMySum (L1 (K1 i))
  ==. MyLeft i
  ==. a
  *** QED
tofMySum a@(MyRight d)
  =   toMySum (fromMySum a)
  ==. toMySum (fromMySum (MyRight d))
  ==. toMySum (R1 (K1 d))
  ==. MyRight d
  ==. a
  *** QED

{-@ fotMySum :: a:RepMySum x
             -> { fromMySum (toMySum a) == a }
@-}
fotMySum :: RepMySum x -> Proof
fotMySum a@(L1 (K1 i))
  =   fromMySum (toMySum a)
  ==. fromMySum (toMySum (L1 (K1 i)))
  ==. fromMySum (MyLeft i)
  ==. L1 (K1 i)
  ==. a
  *** QED
fotMySum a@(R1 (K1 d))
  =   fromMySum (toMySum a)
  ==. fromMySum (toMySum (R1 (K1 d)))
  ==. fromMySum (MyRight d)
  ==. R1 (K1 d)
  ==. a
  *** QED

isoMySum :: Iso (RepMySum x) MySum
isoMySum = Iso toMySum fromMySum tofMySum fotMySum

-- veqMySum :: VerifiedEq MySum
-- veqMySum = veqIso isoMySum $ veqSum (veqK1 veqInt) (veqK1 veqDouble)
