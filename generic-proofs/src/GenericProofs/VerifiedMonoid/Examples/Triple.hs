{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedMonoid.Examples.Triple where


import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedMonoid
import GenericProofs.VerifiedMonoid.Generics
import GenericProofs.VerifiedMonoid.Instances

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
$(deriveIso "RepTriple"
            "toTriple" "fromTriple"
            "tofTriple" "fotTriple"
            "isoTriple"
            ''Triple)

vmonoidTriple :: VerifiedMonoid (Triple Unit Unit Unit)
vmonoidTriple =
    vmonoidIso (isoSym isoTriple)
               $ vmonoidM1
               $ vmonoidM1
               $ vmonoidProd (vmonoidM1 $ vmonoidK1 vmonoidUnit)
               $ vmonoidProd (vmonoidM1 $ vmonoidK1 vmonoidUnit)
                         (vmonoidM1 $ vmonoidK1 vmonoidUnit)

