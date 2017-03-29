{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TypeOperators #-}
module GenericProofs.VerifiedEq.Examples.Product where

import GenericProofs.Combinators
import GenericProofs.Iso
import GenericProofs.VerifiedEq
import GenericProofs.VerifiedEq.Generics
import GenericProofs.VerifiedEq.Instances

import Generics.Deriving.Newtypeless

{-@ data MyProduct = MyProduct { fld1 :: Int, fld2 :: Double } @-}
data MyProduct = MyProduct Int Double

{-@ assume product :: a:(f p)
                   -> b:(g p)
                   -> {v:Product f g p | v == Product a b && select_Product_1 v == a && select_Product_2 v == b } @-}
product :: f p -> g p -> Product f g p
product = Product

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
