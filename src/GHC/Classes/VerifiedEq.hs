{-@ LIQUID "--exactdc"                             @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

{-# LANGUAGE FlexibleInstances #-}

module GHC.Classes.VerifiedEq where

import Language.Haskell.Liquid.ProofCombinators

{-@ class measure eq :: forall a. a -> a -> Bool @-}

{-@ class VerifiedEq a where
      eq :: a -> a -> Bool
      refl :: x:a -> {eq x x}
      sym :: x:a -> y:a -> {eq x y ==> eq y x}
      trans :: x:a -> y:a -> z:a -> {eq x y && eq y z ==> eq x z}
@-}

class VerifiedEq a where
  eq :: a -> a -> Bool
  refl :: a -> Proof
  sym :: a -> a -> Proof
  trans :: a -> a -> a -> Proof

{-@ reflect eqInt @-}
eqInt :: Int -> Int -> Bool
eqInt x y = x == y

{-@ eqIntRefl :: x:Int -> {eqInt x x} @-}
eqIntRefl :: Int -> Proof
eqIntRefl _ = ()

{-@ eqIntSym :: x:Int -> y:Int -> {eqInt x y ==> eqInt y x} @-}
eqIntSym :: Int -> Int -> Proof
eqIntSym _ _ = ()

{-@ eqIntTrans :: x:Int -> y:Int -> z:Int -> {eqInt x y && eqInt y z ==> eqInt x z} @-}
eqIntTrans :: Int -> Int -> Int -> Proof
eqIntTrans _ _ _ = ()

instance VerifiedEq Int where
  {-@ instance measure eq :: Int -> Int -> Bool
      eq x y = x == y
  @-}
  eq    = eqInt
  refl  = eqIntRefl
  sym   = eqIntSym
  trans = eqIntTrans

{-@ data P a b = MkP {p1 :: a, p2 :: b} @-}
data P a b = MkP { p1 :: a, p2 :: b }

{-@ reflect eqPIntInt @-}
eqPIntInt :: P Int Int -> P Int Int -> Bool
eqPIntInt (MkP x y) (MkP z w) = x == z && y == w

{-@ eqPIntIntRefl :: x:P Int Int -> {eqPIntInt x x} @-}
eqPIntIntRefl :: P Int Int -> Proof
eqPIntIntRefl _ = ()

{-@ eqPIntIntSym :: x:P Int Int -> y:P Int Int -> {eqPIntInt x y ==> eqPIntInt y x} @-}
eqPIntIntSym :: P Int Int -> P Int Int -> Proof
eqPIntIntSym _ _ = ()

{-@ eqPIntIntTrans :: x:P Int Int -> y:P Int Int -> z:P Int Int -> {eqPIntInt x y && eqPIntInt y z ==> eqPIntInt x z} @-}
eqPIntIntTrans :: P Int Int -> P Int Int -> P Int Int -> Proof
eqPIntIntTrans _ _ _ = ()

instance VerifiedEq (P Int Int) where
  {-@ instance measure eq :: P Int Int -> P Int Int -> Bool
      eq (MkP x y) (MkP z w) = x == z && y == w
  @-}
  eq    = eqPIntInt
  refl  = eqPIntIntRefl
  sym   = eqPIntIntSym
  trans = eqPIntIntTrans
