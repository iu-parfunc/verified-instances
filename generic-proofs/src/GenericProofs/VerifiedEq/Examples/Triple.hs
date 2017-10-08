{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--noadt"              @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedEq.Examples.Triple where


import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedEq
import GenericProofs.VerifiedEq.Generics
import GenericProofs.VerifiedEq.Instances

import Generics.Deriving.Newtypeless.Base.Internal

data Triple a b c = MkTriple a b c

{-@ axiomatize fromTriple @-}
{-@ axiomatize toTriple @-}
{-@ tofTriple :: a:Triple a b c
              -> { toTriple (fromTriple a) == a }
@-}
{-@ fotTriple :: a:RepTriple a b c x
              -> { fromTriple (toTriple a) == a }
@-}
$(deriveIso "RepTriple"
            "toTriple" "fromTriple"
            "tofTriple" "fotTriple"
            "isoTriple"
            ''Triple)

veqTriple :: VerifiedEq (Triple Int Double Int)
veqTriple =
    veqIso (isoSym isoTriple)
               $ veqM1
               $ veqM1
               $ veqProd (veqM1 $ veqK1 veqInt)
               $ veqProd (veqM1 $ veqK1 veqDouble)
                         (veqM1 $ veqK1 veqInt)

