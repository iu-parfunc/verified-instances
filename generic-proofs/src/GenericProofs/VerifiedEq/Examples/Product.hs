{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
{-# LANGUAGE TypeOperators #-}
module GenericProofs.VerifiedEq.Examples.Product where


import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.Iso
import GenericProofs.VerifiedEq
import GenericProofs.VerifiedEq.Instances

import Generics.Deriving.Newtypeless


{-@ data MyProduct = MyProduct { fld1 :: Int, fld2 :: Double } @-}
data MyProduct = MyProduct Int Double



-- | Begin manual reflection of imported data types:

-- The below refinement is useless as K1 is defined in another file
{- data K1 i c p = K1 { unK1 :: c } -}


-- Instead we manually refine the data constructor and the methods as follows:

{-@ assume K1   :: c:c -> {v:K1 i c p | v == K1 c &&  unK1 v == c && select_K1_1 v == c } @-}
{-@ assume unK1 :: k:K1 i c p -> {v:c | v == unK1 k && v == select_K1_1 k && K1 v == k } @-}

{-@ measure select_K1_1 :: K1 i c p -> c @-}
{-@ measure unK1        :: K1 i c p -> c @-}


-- Same for product
{- data Product f g p = Product (f g) (g p) -}

{-@ assume Product :: a:(f p)
                   -> b:(g p)
                   -> {v:Product f g p | v == Product a b && select_Product_1 v == a && select_Product_2 v == b } @-}

{-@ measure select_Product_1 :: Product f g p -> f p @-}
{-@ measure select_Product_2 :: Product f g p -> g p @-}

-- | END manual reflection of imported data types


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
