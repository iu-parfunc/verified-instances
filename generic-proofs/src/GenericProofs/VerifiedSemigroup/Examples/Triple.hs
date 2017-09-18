{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedSemigroup.Examples.Triple where


import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedSemigroup
import GenericProofs.VerifiedSemigroup.Generics
import GenericProofs.VerifiedSemigroup.Instances

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

vsemigroupTriple :: VerifiedSemigroup (Triple Unit Unit Unit)
vsemigroupTriple =
    vsemigroupIso (isoSym isoTriple)
               $ vsemigroupM1
               $ vsemigroupM1
               $ vsemigroupProd (vsemigroupM1 $ vsemigroupK1 vsemigroupUnit)
               $ vsemigroupProd (vsemigroupM1 $ vsemigroupK1 vsemigroupUnit)
                         (vsemigroupM1 $ vsemigroupK1 vsemigroupUnit)

