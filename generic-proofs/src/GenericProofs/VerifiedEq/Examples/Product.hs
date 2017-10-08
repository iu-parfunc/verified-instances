{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--noadt"              @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module GenericProofs.VerifiedEq.Examples.Product where


import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.TH
import GenericProofs.VerifiedEq
import GenericProofs.VerifiedEq.Generics
import GenericProofs.VerifiedEq.Instances

import Generics.Deriving.Newtypeless.Base.Internal

data MyProduct = MyProduct Int Double

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

veqMyProduct :: VerifiedEq MyProduct
veqMyProduct = veqIso (isoSym isoMyProduct) $ veqM1
                                            $ veqM1
                                            $ veqProd (veqM1 $ veqK1 veqInt)
                                                      (veqM1 $ veqK1 veqDouble)
