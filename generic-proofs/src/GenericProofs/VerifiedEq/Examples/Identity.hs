{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedEq.Examples.Identity
  ( Identity(..)
  , RepIdentity
  , toIdentity
  , fromIdentity
  , tofIdentity
  , fotIdentity
  , isoIdentity
  , veqIdentity
  ) where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedEq
import GenericProofs.VerifiedEq.Generics
import GenericProofs.VerifiedEq.Instances

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

veqIdentity :: VerifiedEq (Identity Int)
veqIdentity = veqIso (isoSym isoIdentity) $ veqM1 $ veqM1 $ veqM1 $ veqK1 veqInt
