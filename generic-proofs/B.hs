-- B.hs
{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
module B where

import A
import K1

import Language.Haskell.Liquid.ProofCombinators

{-@ data MyInt = MyInt { getMyInt :: Int } @-}
data MyInt = MyInt { getMyInt :: Int }
type RepMyInt = Rec0 Int

{-@ axiomatize fromMyInt @-}
fromMyInt :: MyInt -> RepMyInt x
fromMyInt (MyInt x) = K1 x

{-@ axiomatize toMyInt @-}
toMyInt :: RepMyInt x -> MyInt
toMyInt (K1 x) = MyInt x

{-@ tofMyInt :: a:MyInt
             -> { toMyInt (fromMyInt a) == a }
@-}
tofMyInt :: MyInt -> Proof
tofMyInt a@(MyInt x)
  =   toMyInt (fromMyInt a)
  ==. toMyInt (K1 x)
  ==. a
  *** QED

{-@ fotMyInt :: a:RepMyInt x
             -> { fromMyInt (toMyInt a) == a }
@-}
fotMyInt :: RepMyInt x -> Proof
fotMyInt a@(K1 x)
  =   fromMyInt (toMyInt a)
  ==. fromMyInt (MyInt x)
  ==. a
  *** QED
