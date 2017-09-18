{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedFunctor.Examples.Triple where


import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedFunctor
import GenericProofs.VerifiedFunctor.Generics

import Generics.Deriving.Newtypeless.Base.Internal


{-@ data Triple a b c = MkTriple { fld1 :: a, fld2 :: b, fld3 :: c } @-}
data Triple a b c = MkTriple a b c

{-@ axiomatize fromTriple @-}
{-@ axiomatize toTriple @-}
{-@ tofTriple :: a:Triple a b c
              -> { toTriple (fromTriple a) == a }
@-}
{-@ fotTriple :: a:RepTriple a b c x
              -> { fromTriple (toTriple a) == a }
@-}
$(deriveIso1 "RepTriple"
             "toTriple" "fromTriple"
             "tofTriple" "fotTriple"
             "isoTriple"
             ''Triple)

vfunctorTriple :: VerifiedFunctor (Triple a b)
vfunctorTriple =
    vfunctorIso (iso1Sym isoTriple)
  $ vfunctorM1
  $ vfunctorM1
  $ vfunctorProduct (vfunctorM1 vfunctorK1)
                    (vfunctorProduct (vfunctorM1 vfunctorK1)
                                     (vfunctorM1 vfunctorPar1))
