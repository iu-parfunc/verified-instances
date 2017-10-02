{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedMonoid.Examples.Identity
  ( Identity(..)
  , RepIdentity
  , toIdentity
  , fromIdentity
  , tofIdentity
  , fotIdentity
  , isoIdentity
  , vmonoidIdentity
  ) where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedMonoid
import GenericProofs.VerifiedMonoid.Generics
import GenericProofs.VerifiedMonoid.Instances

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

vmonoidIdentity :: VerifiedMonoid (Identity Unit)
vmonoidIdentity = vmonoidIso (isoSym isoIdentity) $ vmonoidM1 $ vmonoidM1 $ vmonoidM1 $ vmonoidK1 vmonoidUnit
