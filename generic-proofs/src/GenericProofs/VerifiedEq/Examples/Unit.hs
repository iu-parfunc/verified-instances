{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
module GenericProofs.VerifiedEq.Examples.Unit where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.VerifiedEq
import GenericProofs.VerifiedEq.Generics

import Generics.Deriving.Newtypeless.Base.Internal

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
