{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
module GenericProofs.Classes where

import GenericProofs.Combinators
import GenericProofs.Iso
import GHC.Generics

{-
class Generic a => GenericIso a where
  repIso :: Iso a (Rep a x)

class Generic1 f => Generic1Iso f where
  rep1Iso :: Iso (f a) (Rep1 f a)
-}

newtype MyInt = MyInt Int
{-@ MyInt :: x:Int -> {v:MyInt | v ~~ x } @-}

type RepMyInt = Rec0 Int

{-@ measure fromMyInt ::   MyInt ->    RepMyInt x @-}
{-@ assume  fromMyInt :: x:MyInt -> {v:RepMyInt x | v ~~ x } @-}
fromMyInt :: MyInt -> RepMyInt x
fromMyInt (MyInt x) = K1 x

{-@ measure toMyInt ::   RepMyInt x ->    MyInt @-}
{-@ assume  toMyInt :: x:RepMyInt x -> {v:MyInt | v ~~ x } @-}
toMyInt :: RepMyInt x -> MyInt
toMyInt (K1 x) = MyInt x

{-@ tofMyInt :: a:MyInt
             -> { toMyInt (fromMyInt a) == a }
@-}
tofMyInt :: MyInt -> Proof
tofMyInt (MyInt x)
  =   toMyInt (fromMyInt (MyInt x))
  ==. toMyInt (K1 x)
  ==. MyInt x
  *** QED
