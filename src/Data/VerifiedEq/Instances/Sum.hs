{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Data.VerifiedEq.Instances.Sum (veqSum, eqSum) where

import Data.VerifiedEq
import Language.Haskell.Liquid.ProofCombinators

{-@ data Either a b = Left a | Right b @-}

{-@ axiomatize eqSum @-}
eqSum :: (a -> a -> Bool) -> (b -> b -> Bool)
      -> Either a b -> Either a b -> Bool
eqSum eqa eqb (Left x) (Left y)   = eqa x y
eqSum eqa eqb (Left x) (Right y)  = False
eqSum eqa eqb (Right x) (Left y)  = False
eqSum eqa eqb (Right x) (Right y) = eqb x y
{-# INLINE eqSum #-}

{-@ eqSumRefl :: eqa:(a -> a -> Bool) -> eqaRefl:(x:a -> { eqa x x })
              -> eqb:(b -> b -> Bool) -> eqbRefl:(y:b -> { eqb y y })
              -> p:Either a b
              -> { eqSum eqa eqb p p }
@-}
eqSumRefl :: (a -> a -> Bool) -> (a -> Proof)
          -> (b -> b -> Bool) -> (b -> Proof)
          -> Either a b -> Proof
eqSumRefl eqa eqaRefl eqb eqbRefl p@(Left x)  = eqaRefl x *** QED
eqSumRefl eqa eqaRefl eqb eqbRefl p@(Right y) = eqbRefl y *** QED

{-@ eqSumSym :: eqa:(a -> a -> Bool) -> eqaSym:(x:a -> y:a -> { eqa x y ==> eqa y x })
             -> eqb:(b -> b -> Bool) -> eqbSym:(x:b -> y:b -> { eqb x y ==> eqb y x })
             -> p:Either a b -> q:Either a b
             -> { eqSum eqa eqb p q ==> eqSum eqa eqb q p }
@-}
eqSumSym :: (a -> a -> Bool) -> (a -> a -> Proof)
         -> (b -> b -> Bool) -> (b -> b -> Proof)
         -> Either a b -> Either a b -> Proof
eqSumSym eqa eqaSym eqb eqbSym p@(Left x) q@(Left y) =
      eqSum eqa eqb p q
  ==. eqa y x ? eqaSym x y
  ==. eqSum eqa eqb q p
  *** QED
eqSumSym eqa eqaSym eqb eqbSym p@(Left x) q@(Right y) =
      eqSum eqa eqb p q
  *** QED
eqSumSym eqa eqaSym eqb eqbSym p@(Right x) q@(Left y) =
      eqSum eqa eqb p q
  *** QED
eqSumSym eqa eqaSym eqb eqbSym p@(Right x) q@(Right y) =
      eqSum eqa eqb p q
  ==. eqb y x ? eqbSym x y
  ==. eqSum eqa eqb q p
  *** QED

{-@ eqSumTrans :: eqa:(a -> a -> Bool) -> eqaTrans:(x:a -> y:a -> z:a -> { eqa x y && eqa y z ==> eqa x z })
               -> eqb:(b -> b -> Bool) -> eqbTrans:(x:b -> y:b -> z:b -> { eqb x y && eqb y z ==> eqb x z })
               -> p:Either a b -> q:Either a b -> r:Either a b
               -> { eqSum eqa eqb p q && eqSum eqa eqb q r ==> eqSum eqa eqb p r }
@-}
eqSumTrans :: (a -> a -> Bool) -> (a -> a -> a -> Proof)
           -> (b -> b -> Bool) -> (b -> b -> b -> Proof)
           -> Either a b -> Either a b -> Either a b -> Proof
eqSumTrans eqa eqaTrans eqb eqbTrans p@(Left x) q@(Left y) r@(Left z) =
      (eqSum eqa eqb p q && eqSum eqa eqb q r)
  ==. eqa x z ? eqaTrans x y z
  ==. eqSum eqa eqb p r
  *** QED
eqSumTrans eqa eqaTrans eqb eqbTrans p@(Left x) q@(Left y) r@(Right z) =
      (eqSum eqa eqb p q && eqSum eqa eqb q r)
  *** QED
eqSumTrans eqa eqaTrans eqb eqbTrans p@(Left x) q@(Right y) r@(Left z) =
      (eqSum eqa eqb p q && eqSum eqa eqb q r)
  *** QED
eqSumTrans eqa eqaTrans eqb eqbTrans p@(Left x) q@(Right y) r@(Right z) =
      (eqSum eqa eqb p q && eqSum eqa eqb q r)
  *** QED
eqSumTrans eqa eqaTrans eqb eqbTrans p@(Right x) q@(Left y) r@(Left z) =
      (eqSum eqa eqb p q && eqSum eqa eqb q r)
  *** QED
eqSumTrans eqa eqaTrans eqb eqbTrans p@(Right x) q@(Left y) r@(Right z) =
      (eqSum eqa eqb p q && eqSum eqa eqb q r)
  *** QED
eqSumTrans eqa eqaTrans eqb eqbTrans p@(Right x) q@(Right y) r@(Left z) =
      (eqSum eqa eqb p q && eqSum eqa eqb q r)
  *** QED
eqSumTrans eqa eqaTrans eqb eqbTrans p@(Right x) q@(Right y) r@(Right z) =
      (eqSum eqa eqb p q && eqSum eqa eqb q r)
  ==. eqb x z ? eqbTrans x y z
  ==. eqSum eqa eqb p r
  *** QED

{-@ veqSum :: VerifiedEq a -> VerifiedEq b -> VerifiedEq (Either a b) @-}
veqSum :: VerifiedEq a -> VerifiedEq b -> VerifiedEq (Either a b)
veqSum (VerifiedEq eqa eqaRefl eqaSym eqaTrans) (VerifiedEq eqb eqbRefl eqbSym eqbTrans) =
  VerifiedEq (eqSum eqa eqb)
             (eqSumRefl eqa eqaRefl eqb eqbRefl)
             (eqSumSym eqa eqaSym eqb eqbSym)
             (eqSumTrans eqa eqaTrans eqb eqbTrans)
