{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--noadt"              @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedFunctor.Examples.Identity where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedFunctor
import GenericProofs.VerifiedFunctor.Generics

import Generics.Deriving.Newtypeless.Base.Internal

-- Morally a newtype, but in practice, not.
{-@ data Identity a = Identity { getIdentity :: a } @-}
data Identity a = Identity { runIdentity :: a }

{-
type RepId = Par1

{-@ axiomatize fromId @-}
fromId :: Id a -> RepId a
fromId (Id a) = Par1 a

{-@ axiomatize toId @-}
toId :: RepId a -> Id a
toId (Par1 a) = Id a

{-@ tofId :: x:Id a
          -> { toId (fromId x) == x }
@-}
tofId :: Id a -> Proof
tofId x@(Id a)
  =   toId (fromId x)
  ==. toId (Par1 a)
  ==. x
  *** QED

{-@ fotId :: x:RepId a
          -> { fromId (toId x) == x }
@-}
fotId :: RepId a -> Proof
fotId x@(Par1 a)
  =   fromId (toId x)
  ==. fromId (Id a)
  ==. x
  *** QED
-}

{-@ axiomatize fromIdentity @-}
{-@ axiomatize toIdentity @-}
{-@ tofIdentity1 :: x:Identity a
                 -> { toIdentity (fromIdentity x) == x }
@-}
{-@ fotIdentity1 :: x:RepIdentity1 a
                 -> { fromIdentity (toIdentity x) == x }
@-}
$(deriveIso1 "RepIdentity1"
             "toIdentity" "fromIdentity"
             "tofIdentity1" "fotIdentity1"
             "isoIdentity1"
             ''Identity)

vfunctorIdentity :: VerifiedFunctor Identity
vfunctorIdentity = vfunctorIso (iso1Sym isoIdentity1)
                 $ vfunctorM1 $ vfunctorM1 $ vfunctorM1 vfunctorPar1
