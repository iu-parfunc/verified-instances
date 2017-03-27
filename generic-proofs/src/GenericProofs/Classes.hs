{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
-- {-@ LIQUID "--prune-unsorted"     @-}
module GenericProofs.Classes where

import GenericProofs.Combinators
import GenericProofs.Iso
import GenericProofs.VerifiedEq
import GenericProofs.VerifiedEq.Generics
import GenericProofs.VerifiedEq.Instances

import Generics.Deriving.Newtypeless

{-
class Generic a => GenericIso a where
  repIso :: Iso a (Rep a x)

class Generic1 f => Generic1Iso f where
  rep1Iso :: Iso (f a) (Rep1 f a)
-}

{-@ data MyInt = MyInt { getMyInt :: Int } @-}
data MyInt = MyInt { getMyInt :: Int }

{-@ data K1 i c p = K1 { unK1 :: c } @-}

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
  ==. toMyInt (fromMyInt (MyInt x))
  ==. toMyInt (K1 x)
  ==. MyInt x
  ==. a
  *** QED

{-
{-@ fotMyInt :: from':(x:MyInt -> {v:RepMyInt x | v ~~ x})
             -> to':(x:RepMyInt x -> {v:MyInt | v ~~ x})
             -> a:RepMyInt x
             -> { from' (to' a) == a }
@-}
fotMyInt :: (MyInt -> RepMyInt x) -> (RepMyInt x -> MyInt) -> RepMyInt x -> Proof
fotMyInt from' to' (K1 x)
  =   from' (to' (K1 x))
  ==. from' (MyInt x)
  ==. K1 x
  *** QED

isoMyInt :: Iso MyInt (RepMyInt x)
isoMyInt = Iso fromMyInt toMyInt (fotMyInt fromMyInt toMyInt)
                                 (tofMyInt fromMyInt toMyInt)

veqMyInt :: VerifiedEq MyInt
veqMyInt = veqContra fromMyInt $ veqK1 veqInt
-}
