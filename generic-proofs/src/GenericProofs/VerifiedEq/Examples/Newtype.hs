{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
module GenericProofs.VerifiedEq.Examples.Newtype where

import GenericProofs.Combinators
import GenericProofs.Iso
import GenericProofs.VerifiedEq
import GenericProofs.VerifiedEq.Generics
import GenericProofs.VerifiedEq.Instances

import Generics.Deriving.Newtypeless

-- Morally a newtype, but in practice, not.
{-@ data MyInt = MyInt { getMyInt :: Int } @-}
data MyInt = MyInt { getMyInt :: Int }

-- The below refinement is useless as K1 is defined in another file
{- data K1 i c p = K1 { unK1 :: c } @-}

{-@ assume k1   :: c:c -> {v:K1 i c p | v == K1 c &&  unK1 v == c && select_K1_1 v == c } @-}
k1 :: c -> K1 i c p
k1 = K1

{-
{-@ assume unk1 :: k:K1 i c p -> {v:c | v == unK1 k && K1 v == k } @-}
unk1 :: K1 i c p -> c
unk1 = unK1
-}

type RepMyInt = Rec0 Int

{-@ axiomatize fromMyInt @-}
fromMyInt :: MyInt -> RepMyInt x
fromMyInt (MyInt x) = K1 x

{-@ axiomatize toMyInt @-}
toMyInt :: RepMyInt x -> MyInt
toMyInt (K1 x) = MyInt x

{-@ tofMyInt :: a:MyInt
             -> { toMyInt (fromMyInt a) == a }
@-}
tofMyInt :: MyInt -> Proof
tofMyInt a@(MyInt x)
  =   toMyInt (fromMyInt a)
  ==. toMyInt (k1 x)
  ==. a
  *** QED

{-@ fotMyInt :: a:RepMyInt x
             -> { fromMyInt (toMyInt a) == a }
@-}
fotMyInt :: RepMyInt x -> Proof
fotMyInt a@(K1 x)
  =   fromMyInt (toMyInt a)
  ==. fromMyInt (MyInt x)
  ==. a
  *** QED

isoMyInt :: Iso MyInt (RepMyInt x)
isoMyInt = Iso fromMyInt toMyInt fotMyInt tofMyInt

veqMyInt :: VerifiedEq MyInt
veqMyInt = veqContra fromMyInt $ veqK1 veqInt
