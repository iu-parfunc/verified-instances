{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--noadt"              @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedSemigroup.Examples.Identity
  ( Identity(..)
  , RepIdentity
  , toIdentity
  , fromIdentity
  , tofIdentity
  , fotIdentity
  , isoIdentity
  , vsemigroupIdentity
  ) where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedSemigroup
import GenericProofs.VerifiedSemigroup.Generics
import GenericProofs.VerifiedSemigroup.Instances

import Generics.Deriving.Newtypeless.Base.Internal

-- Morally a newtype, but in practice, not.
{-@ data Identity a = Identity { getIdentity :: a } @-}
data Identity a = Identity { getIdentity :: a }

{-@ axiomatize fromIdentity @-}
{-@ axiomatize toIdentity @-}
{-@ tofIdentity :: a:Identity
                -> { toIdentity (fromIdentity a) == a }
@-}
{-@ fotIdentity :: a:RepIdentity a x
                -> { fromIdentity (toIdentity a) == a }
@-}
$(deriveIso "RepIdentity"
            "toIdentity" "fromIdentity"
            "tofIdentity" "fotIdentity"
            "isoIdentity"
            ''Identity)

vsemigroupIdentity :: VerifiedSemigroup (Identity Unit)
vsemigroupIdentity = vsemigroupIso (isoSym isoIdentity) $ vsemigroupM1 $ vsemigroupM1 $ vsemigroupM1 $ vsemigroupK1 vsemigroupUnit
