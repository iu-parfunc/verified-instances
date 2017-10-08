{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--noadt"              @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}
module GenericProofs.VerifiedOrd.Examples.Identity
  ( Identity(..)
  , RepIdentity
  , toIdentity
  , fromIdentity
  , tofIdentity
  , fotIdentity
  , isoIdentity
  , vordIdentity
  ) where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedOrd
import GenericProofs.VerifiedOrd.Generics
import GenericProofs.VerifiedOrd.Instances

import Generics.Deriving.Newtypeless.Base.Internal

-- Morally a newtype, but in practice, not.
{-@ data Identity a = Identity { getIdentity :: a } @-}
data Identity a = Identity { getIdentity :: a } deriving (Eq)

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

vordIdentity :: VerifiedOrd (Identity Int)
vordIdentity = vordIso (isoSym isoIdentity) $ vordM1 $ vordM1 $ vordM1 $ vordK1 vordInt
