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
                   -> {v:Product f g p | v == Product a b } @-}
product :: f p -> g p -> Product f g p
product = Product

type RepMyProduct = Product (Rec0 Int) (Rec0 Double)

{-@ axiomatize fromMyProduct @-}
fromMyProduct :: MyProduct -> RepMyProduct x
fromMyProduct (MyProduct i d) = Product (K1 i) (K1 d)

{-@ axiomatize toMyProduct @-}
toMyProduct :: RepMyProduct x -> MyProduct
toMyProduct (Product (K1 i) (K1 d)) = MyProduct i d

{-
{-@ tofProduct :: a:Product
               -> { toProduct (fromProduct a) == a }
@-}
tofProduct :: Product -> Proof
tofProduct a@(MkProduct i d)
  =   toProduct (fromProduct a)
  ==. toProduct (K1 i :*: K1 d)
  ==. MkProduct i d
  ==. a
  *** QED
-}

{-
{-@ fotProduct :: a:RepProduct x
               -> { fromProduct (toProduct a) == a }
@-}
fotProduct :: RepProduct x -> Proof
fotProduct a@(K1 i :*: K1 d)
  =   fromProduct (toProduct a)
  ==. fromProduct (toProduct (K1 i :*: K1 d))
  ==. fromProduct (MkProduct i d)
  ==. K1 i :*: K1 d
  ==. a
  *** QED
-}

