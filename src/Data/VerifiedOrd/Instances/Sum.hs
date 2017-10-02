{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Data.VerifiedOrd.Instances.Sum (vordSum, leqSum) where

import Data.VerifiableConstraint
import Data.VerifiedEq
import Data.VerifiedEq.Instances
import Data.VerifiedOrd
import Language.Haskell.Liquid.ProofCombinators

{-@ data Either a b = Left a | Right b @-}

{-@ axiomatize leqSum @-}
leqSum :: (a -> a -> Bool) -> (b -> b -> Bool)
       -> Either a b -> Either a b -> Bool
leqSum leqa leqb (Left x) (Left y)   = leqa x y
leqSum leqa leqb (Left x) (Right y)  = True
leqSum leqa leqb (Right x) (Left y)  = False
leqSum leqa leqb (Right x) (Right y) = leqb x y
{-# INLINE leqSum #-}

{-@ leqSumRefl :: leqa:(a -> a -> Bool) -> leqaRefl:(x:a -> { leqa x x })
               -> leqb:(b -> b -> Bool) -> leqbRefl:(y:b -> { leqb y y })
               -> p:Either a b
               -> { leqSum leqa leqb p p }
@-}
leqSumRefl :: (a -> a -> Bool) -> (a -> Proof)
           -> (b -> b -> Bool) -> (b -> Proof)
           -> Either a b -> Proof
leqSumRefl leqa leqaRefl leqb leqbRefl p@(Left x)  = leqaRefl x
leqSumRefl leqa leqaRefl leqb leqbRefl p@(Right y) = leqbRefl y

{-@ leqSumAntisym :: leqa:(a -> a -> Bool) -> leqaAntisym:(x:a -> y:a -> { leqa x y && leqa y x ==> x == y })
                  -> leqb:(b -> b -> Bool) -> leqbAntisym:(x:b -> y:b -> { leqb x y && leqb y x ==> x == y })
                  -> VerifiedEq a -> VerifiedEq b
                  -> p:Either a b -> q:Either a b
                  -> { leqSum leqa leqb p q && leqSum leqa leqb q p ==> p == q }
@-}
leqSumAntisym :: (a -> a -> Bool) -> (a -> a -> Proof)
              -> (b -> b -> Bool) -> (b -> b -> Proof)
              -> VerifiedEq a -> VerifiedEq b
              -> Either a b -> Either a b -> Proof
leqSumAntisym leqa leqaAntisym leqb leqbAntisym veqa veqb p@(Left x) q@(Left y) =
      using (VEq veqa)
    $ (leqSum leqa leqb p q && leqSum leqa leqb q p)
  ==. x == y ? leqaAntisym x y
  *** QED
leqSumAntisym leqa leqaAntisym leqb leqbAntisym veqa veqb p@(Left x) q@(Right y) =
      using (VEq veqa)
    $ using (VEq veqb)
    $ (leqSum leqa leqb p q && leqSum leqa leqb q p)
  *** QED
leqSumAntisym leqa leqaAntisym leqb leqbAntisym veqa veqb p@(Right x) q@(Left y) =
      using (VEq veqa)
    $ using (VEq veqb)
    $ (leqSum leqa leqb p q && leqSum leqa leqb q p)
  *** QED
leqSumAntisym leqa leqaAntisym leqb leqbAntisym veqa veqb p@(Right x) q@(Right y) =
      using (VEq veqb)
    $ (leqSum leqa leqb p q && leqSum leqa leqb q p)
  ==. x == y ? leqbAntisym x y
  *** QED

{-@ leqSumTrans :: leqa:(a -> a -> Bool) -> leqaTrans:(x:a -> y:a -> z:a -> { leqa x y && leqa y z ==> leqa x z })
                -> leqb:(b -> b -> Bool) -> leqbTrans:(x:b -> y:b -> z:b -> { leqb x y && leqb y z ==> leqb x z })
                -> p:Either a b -> q:Either a b -> r:Either a b
                -> { leqSum leqa leqb p q && leqSum leqa leqb q r ==> leqSum leqa leqb p r }
@-}
leqSumTrans :: (a -> a -> Bool) -> (a -> a -> a -> Proof)
            -> (b -> b -> Bool) -> (b -> b -> b -> Proof)
            -> Either a b -> Either a b -> Either a b -> Proof
leqSumTrans leqa leqaTrans leqb leqbTrans p@(Left x) q@(Left y) r@(Left z) =
      (leqSum leqa leqb p q && leqSum leqa leqb q r)
  ==. leqa x z ? leqaTrans x y z
  ==. leqSum leqa leqb p r
  *** QED
leqSumTrans leqa leqaTrans leqb leqbTrans p@(Left x) q@(Left y) r@(Right z) =
      (leqSum leqa leqb p q && leqSum leqa leqb q r)
  ==. leqSum leqa leqb p r
  *** QED
leqSumTrans leqa leqaTrans leqb leqbTrans p@(Left x) q@(Right y) r@(Left z) =
      (leqSum leqa leqb p q && leqSum leqa leqb q r)
  ==. leqSum leqa leqb p r
  *** QED
leqSumTrans leqa leqaTrans leqb leqbTrans p@(Left x) q@(Right y) r@(Right z) =
      (leqSum leqa leqb p q && leqSum leqa leqb q r)
  ==. leqSum leqa leqb p r
  *** QED
leqSumTrans leqa leqaTrans leqb leqbTrans p@(Right x) q@(Left y) r@(Left z) =
      (leqSum leqa leqb p q && leqSum leqa leqb q r)
  ==. leqSum leqa leqb p r
  *** QED
leqSumTrans leqa leqaTrans leqb leqbTrans p@(Right x) q@(Left y) r@(Right z) =
      (leqSum leqa leqb p q && leqSum leqa leqb q r)
  ==. leqSum leqa leqb p r
  *** QED
leqSumTrans leqa leqaTrans leqb leqbTrans p@(Right x) q@(Right y) r@(Left z) =
      (leqSum leqa leqb p q && leqSum leqa leqb q r)
  ==. leqSum leqa leqb p r
  *** QED
leqSumTrans leqa leqaTrans leqb leqbTrans p@(Right x) q@(Right y) r@(Right z) =
      (leqSum leqa leqb p q && leqSum leqa leqb q r)
  ==. leqb x z ? leqbTrans x y z
  ==. leqSum leqa leqb p r
  *** QED

{-@ leqSumTotal :: leqa:(a -> a -> Bool) -> leqaTotal:(x:a -> y:a -> { leqa x y || leqa y x })
                -> leqb:(b -> b -> Bool) -> leqbTotal:(x:b -> y:b -> { leqb x y || leqb y x })
                -> p:Either a b -> q:Either a b
                -> { leqSum leqa leqb p q || leqSum leqa leqb q p }
@-}
leqSumTotal :: (a -> a -> Bool) -> (a -> a -> Proof)
            -> (b -> b -> Bool) -> (b -> b -> Proof)
            -> Either a b -> Either a b -> Proof
leqSumTotal leqa leqaTotal leqb leqbTotal p@(Left x) q@(Left y) =
      (leqSum leqa leqb p q || leqSum leqa leqb q p)
  ==. True ? leqaTotal x y
  *** QED
leqSumTotal leqa leqaTotal leqb leqbTotal p@(Left x) q@(Right y) =
      (leqSum leqa leqb p q || leqSum leqa leqb q p)
  *** QED
leqSumTotal leqa leqaTotal leqb leqbTotal p@(Right x) q@(Left y) =
      (leqSum leqa leqb p q || leqSum leqa leqb q p)
  *** QED
leqSumTotal leqa leqaTotal leqb leqbTotal p@(Right x) q@(Right y) =
      (leqSum leqa leqb p q || leqSum leqa leqb q p)
  ==. True ? leqbTotal x y
  *** QED

vordSum :: VerifiedOrd a -> VerifiedOrd b -> VerifiedOrd (Either a b)
vordSum (VerifiedOrd leqa leqaRefl leqaAntisym leqaTrans leqaTotal veqa) (VerifiedOrd leqb leqbRefl leqbAntisym leqbTrans leqbTotal veqb) =
  VerifiedOrd
    (leqSum leqa leqb)
    (leqSumRefl leqa leqaRefl leqb leqbRefl)
    (leqSumAntisym leqa leqaAntisym leqb leqbAntisym veqa veqb)
    (leqSumTrans leqa leqaTrans leqb leqbTrans)
    (leqSumTotal leqa leqaTotal leqb leqbTotal)
    (veqSum veqa veqb)
