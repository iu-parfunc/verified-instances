{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
module GenericProofs.VerifiedSemigroup.Examples.Newtype where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.VerifiedSemigroup
import GenericProofs.VerifiedSemigroup.Generics
import GenericProofs.VerifiedSemigroup.Instances

import Generics.Deriving.Newtypeless

-- Morally a newtype, but in practice, not.
{-@ data WrapUnit = WrapUnit { runMyUnit :: Unit } @-}
data WrapUnit = WrapUnit { runMyUnit :: Unit }

type RepWrapUnit = D1 D1WrapUnit (C1 C1_0WrapUnit (S1 S1_0_0WrapUnit (Rec0 Unit)))

data D1WrapUnit
data C1_0WrapUnit
data S1_0_0WrapUnit

{-@ axiomatize fromWrapUnit @-}
fromWrapUnit :: WrapUnit -> RepWrapUnit x
fromWrapUnit (WrapUnit x) = M1 (M1 (M1 (K1 x)))

{-@ axiomatize toWrapUnit @-}
toWrapUnit :: RepWrapUnit x -> WrapUnit
toWrapUnit (M1 (M1 (M1 (K1 x)))) = WrapUnit x

{-@ tofWrapUnit :: a:WrapUnit
                -> { toWrapUnit (fromWrapUnit a) == a }
@-}
tofWrapUnit :: WrapUnit -> Proof
tofWrapUnit a@(WrapUnit x)
  =   toWrapUnit (fromWrapUnit a)
  ==. toWrapUnit (M1 (M1 (M1 (K1 x))))
  ==. a
  *** QED

{-@ fotWrapUnit :: a:RepWrapUnit x
                -> { fromWrapUnit (toWrapUnit a) == a }
@-}
fotWrapUnit :: RepWrapUnit x -> Proof
fotWrapUnit a@(M1 (M1 (M1 (K1 x))))
  =   fromWrapUnit (toWrapUnit a)
  ==. fromWrapUnit (WrapUnit x)
  ==. a
  *** QED

isoWrapUnit :: Iso WrapUnit (RepWrapUnit x)
isoWrapUnit = Iso fromWrapUnit toWrapUnit fotWrapUnit tofWrapUnit

vsemigroupWrapUnit :: VerifiedSemigroup WrapUnit
vsemigroupWrapUnit = vsemigroupIso (isoSym isoWrapUnit)
                   $ vsemigroupM1
                   $ vsemigroupM1
                   $ vsemigroupM1
                   $ vsemigroupK1 vsemigroupUnit
