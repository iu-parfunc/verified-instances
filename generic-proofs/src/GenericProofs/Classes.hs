{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
-- {-@ LIQUID "--prune-unsorted"     @-}
module GenericProofs.Classes where

import GenericProofs.Combinators
import GenericProofs.Iso
-- import GenericProofs.VerifiedEq
-- import GenericProofs.VerifiedEq.Generics
-- import GenericProofs.VerifiedEq.Instances
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
{-@ assume  fromMyInt :: x:MyInt -> {v:RepMyInt x | v ~~ x && v ~~ fromMyInt x } @-}
fromMyInt :: MyInt -> RepMyInt x
fromMyInt (MyInt x) = K1 x

{-@ measure toMyInt ::   RepMyInt x ->    MyInt @-}
{-@ assume  toMyInt :: x:RepMyInt x -> {v:MyInt | v ~~ x && v ~~ toMyInt x } @-}
toMyInt :: RepMyInt x -> MyInt
toMyInt (K1 x) = MyInt x

{-@ tofMyInt :: from':(x:MyInt -> {v:RepMyInt x | v ~~ x})
             -> to':(x:RepMyInt x -> {v:MyInt | v ~~ x})
             -> a:MyInt
             -> { to' (from' a) == a }
@-}
tofMyInt :: (MyInt -> RepMyInt x) -> (RepMyInt x -> MyInt) -> MyInt -> Proof
tofMyInt from' to' (MyInt x)
  =   to' (from' (MyInt x))
  ==. to' (K1 x)
  ==. MyInt x
  *** QED

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

{-
veqMyInt :: VerifiedEq MyInt
veqMyInt = veqContra _ $ veqK1 veqInt
-}
