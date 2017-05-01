{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TypeOperators #-}
module GenericProofs.VerifiedEq.Examples.Product where


import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.VerifiedEq
-- import GenericProofs.VerifiedEq.Generics        (veqK1, veqProd)
import GenericProofs.VerifiedEq.Instances

import Generics.Deriving.Newtypeless


{-@ data MyProduct = MyProduct { fld1 :: Int, fld2 :: Double } @-}
data MyProduct = MyProduct Int Double

type RepMyProduct = Product (Rec0 Int) (Rec0 Double)

{-@ axiomatize fromMyProduct @-}
fromMyProduct :: MyProduct -> RepMyProduct x
fromMyProduct (MyProduct i d) = Product (K1 i) (K1 d)

{-@ axiomatize toMyProduct @-}
toMyProduct :: RepMyProduct x -> MyProduct
toMyProduct (Product (K1 i) (K1 d)) = MyProduct i d

{-@ tofMyProduct :: a:MyProduct
                 -> { toMyProduct (fromMyProduct a) == a }
@-}
tofMyProduct :: MyProduct -> Proof
tofMyProduct a@(MyProduct i d)
  =   toMyProduct (fromMyProduct a)
  ==. toMyProduct (Product (K1 i) (K1 d))
  ==. MyProduct i d
  ==. a
  *** QED

{-@ fotMyProduct :: a:RepMyProduct x
                 -> { fromMyProduct (toMyProduct a) == a }
@-}
fotMyProduct :: RepMyProduct x -> Proof
fotMyProduct a@(Product (K1 i) (K1 d))
  =   fromMyProduct (toMyProduct a)
  ==. fromMyProduct (toMyProduct (Product (K1 i) (K1 d)))
  ==. fromMyProduct (MyProduct i d)
  ==. Product (K1 i) (K1 d)
  ==. a
  *** QED

isoMyProduct :: Iso (RepMyProduct x) MyProduct
isoMyProduct = Iso toMyProduct fromMyProduct tofMyProduct fotMyProduct

-- veqMyProduct :: VerifiedEq MyProduct
-- veqMyProduct = veqIso isoMyProduct $ veqProd (veqK1 veqInt) (veqK1 veqDouble)
