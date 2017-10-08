{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--noadt"              @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}
module GenericProofs.VerifiedOrd.Examples.Product where


import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedOrd
import GenericProofs.VerifiedOrd.Generics
import GenericProofs.VerifiedOrd.Instances

import Generics.Deriving.Newtypeless.Base.Internal


{-@ data MyProduct = MyProduct { fld1 :: Int, fld2 :: Double } @-}
data MyProduct = MyProduct Int Double deriving (Eq)

{-@ axiomatize fromMyProduct @-}
{-@ axiomatize toMyProduct @-}
{-@ tofMyProduct :: a:MyProduct
                 -> { toMyProduct (fromMyProduct a) == a }
@-}
{-@ fotMyProduct :: a:RepMyProduct x
                 -> { fromMyProduct (toMyProduct a) == a }
@-}
$(deriveIso "RepMyProduct"
            "toMyProduct" "fromMyProduct"
            "tofMyProduct" "fotMyProduct"
            "isoMyProduct"
            ''MyProduct)

vordMyProduct :: VerifiedOrd MyProduct
vordMyProduct = vordIso (isoSym isoMyProduct) $ vordM1
                                              $ vordM1
                                              $ vordProd (vordM1 $ vordK1 vordInt)
                                                         (vordM1 $ vordK1 vordDouble)
