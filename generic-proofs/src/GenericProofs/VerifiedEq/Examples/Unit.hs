{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
module GenericProofs.VerifiedEq.Examples.Unit where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.VerifiedEq
import GenericProofs.VerifiedEq.Generics

import Generics.Deriving.Newtypeless

{-@ data MyUnit = MyUnit @-}
data MyUnit = MyUnit

type RepMyUnit = U1

{-@ axiomatize fromMyUnit @-}
fromMyUnit :: MyUnit -> RepMyUnit x
fromMyUnit MyUnit = U1

{-@ axiomatize toMyUnit @-}
toMyUnit :: RepMyUnit x -> MyUnit
toMyUnit U1 = MyUnit

{-@ tofMyUnit :: a:MyUnit
              -> { toMyUnit (fromMyUnit a) == a }
@-}
tofMyUnit :: MyUnit -> Proof
tofMyUnit a@MyUnit
  =   toMyUnit (fromMyUnit a)
  ==. toMyUnit U1
  ==. a
  *** QED

{-@ fotMyUnit :: a:RepMyUnit x
              -> { fromMyUnit (toMyUnit a) == a }
@-}
fotMyUnit :: RepMyUnit x -> Proof
fotMyUnit a@U1
  =   fromMyUnit (toMyUnit a)
  ==. fromMyUnit MyUnit
  ==. a
  *** QED

isoMyUnit :: Iso MyUnit (RepMyUnit x)
isoMyUnit = Iso fromMyUnit toMyUnit fotMyUnit tofMyUnit

veqMyUnit :: VerifiedEq MyUnit
veqMyUnit = veqContra fromMyUnit veqU1

{-
-- Morally a newtype, but in practice, not.
{-@ data MyInt = MyInt { getMyInt :: Int } @-}
data MyInt = MyInt { getMyInt :: Int }

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
  ==. toMyInt (K1 x)
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
-}
