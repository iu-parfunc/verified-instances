{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
module GenericProofs.VerifiedFunctor.Examples.Identity where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
-- import GenericProofs.VerifiedFunctor
-- import GenericProofs.VerifiedFunctor.Generics

import Generics.Deriving.Newtypeless

{-@ data Id a = Id { runId :: a } @-}
data Id a = Id { runId :: a }

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

isoId :: Iso1 Id RepId
isoId = Iso1 fromId toId fotId tofId
