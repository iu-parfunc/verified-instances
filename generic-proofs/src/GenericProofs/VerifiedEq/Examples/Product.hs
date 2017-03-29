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

{-@ data Product = MkProduct { fld1 :: Int, fld2 :: Double } @-}
data Product = MkProduct Int Double

type Prod = (:*:)

{-@ assume genProd :: a:(f p)
                   -> b:(g p)
                   -> {v:Prod f g p | v == a :*: b } @-}
genProd :: f p -> g p -> (f :*: g) p
genProd = (:*:)

type RepProduct = Rec0 Int :*: Rec0 Double

{-@ axiomatize fromProduct @-}
fromProduct :: Product -> RepProduct x
fromProduct (MkProduct i d) = K1 i :*: K1 d

{-@ axiomatize toProduct @-}
toProduct :: RepProduct x -> Product
toProduct (K1 i :*: K1 d) = MkProduct i d

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

