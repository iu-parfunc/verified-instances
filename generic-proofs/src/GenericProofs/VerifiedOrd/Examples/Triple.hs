{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}
module GenericProofs.VerifiedOrd.Examples.Triple where


import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedOrd
import GenericProofs.VerifiedOrd.Generics
import GenericProofs.VerifiedOrd.Instances

import Generics.Deriving.Newtypeless.Base.Internal


{-@ data Triple a b c = MkTriple { fld1 :: a, fld2 :: b, fld3 :: c } @-}
data Triple a b c = MkTriple a b c deriving (Eq)

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

vordTriple :: VerifiedOrd (Triple Int Double Int)
vordTriple =
    vordIso (isoSym isoTriple)
               $ vordM1
               $ vordM1
               $ vordProd (vordM1 $ vordK1 vordInt)
               $ vordProd (vordM1 $ vordK1 vordDouble)
                          (vordM1 $ vordK1 vordInt)
