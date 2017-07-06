{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Data.VerifiedOrd.Instances.Prod (vordProd, leqProd) where

import Data.VerifiableConstraint
import Data.VerifiedEq
import Data.VerifiedEq.Instances
import Data.VerifiedOrd
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize leqProd @-}
leqProd :: Eq a
        => (a -> a -> Bool) -> (b -> b -> Bool)
        -> (a, b) -> (a, b) -> Bool
leqProd leqa leqb (x1, y1) (x2, y2) =
  if x1 == x2
    then leqb y1 y2
    else leqa x1 x2
{-# INLINE leqProd #-}

{-@ leqProdRefl :: Eq a
                => leqa:(a -> a -> Bool) -> leqaRefl:(x:a -> { leqa x x })
                -> leqb:(b -> b -> Bool) -> leqbRefl:(y:b -> { leqb y y })
                -> p:(a, b) -> { leqProd leqa leqb p p }
@-}
leqProdRefl :: Eq a
            => (a -> a -> Bool) -> (a -> Proof)
            -> (b -> b -> Bool) -> (b -> Proof)
            -> (a, b) -> Proof
leqProdRefl leqa leqaRefl leqb leqbRefl p@(x, y) = leqbRefl y

{-@ leqProdAntisym :: (Eq a, Eq b)
                   => leqa:(a -> a -> Bool)
                   -> leqaAntisym:(x:a -> y:a -> { leqa x y && leqa y x ==> x == y })
                   -> leqb:(b -> b -> Bool)
                   -> leqbAntisym:(x:b -> y:b -> { leqb x y && leqb y x ==> x == y })
                   -> p:(a, b) -> q:(a, b)
                   -> { leqProd leqa leqb p q && leqProd leqa leqb q p ==> p == q }
@-}
leqProdAntisym :: (Eq a, Eq b)
               => (a -> a -> Bool) -> (a -> a -> Proof)
               -> (b -> b -> Bool) -> (b -> b -> Proof)
               -> (a, b) -> (a, b) -> Proof
leqProdAntisym leqa leqaAntisym leqb leqbAntisym p@(x1, y1) q@(x2, y2) =
      (leqProd leqa leqb p q && leqProd leqa leqb q p)
  ==. ((if x1 == x2 then leqb y1 y2 else leqa x1 x2) && (if x2 == x1 then leqb y2 y1 else leqa x2 x1))
  ==. (if x1 == x2 then leqb y1 y2 && leqb y2 y1 else leqa x1 x2 && leqa x2 x1)
  ==. (if x1 == x2 then y1 == y2 else leqa x1 x2 && leqa x2 x1) ? leqbAntisym y1 y2
  ==. (if x1 == x2 then y1 == y2 else x1 == x2)                 ? leqaAntisym x1 x2
  ==. (x1 == x2 && y1 == y2)
  ==. (p == q)
  *** QED

{-@ leqProdTrans :: Eq a
                 => leqa:(a -> a -> Bool)
                 -> leqaAntisym:(x:a -> y:a -> { leqa x y && leqa y x ==> x == y })
                 -> leqaTrans:(x:a -> y:a -> z:a -> { leqa x y && leqa y z ==> leqa x z })
                 -> leqb:(b -> b -> Bool)
                 -> leqbTrans:(x:b -> y:b -> z:b -> { leqb x y && leqb y z ==> leqb x z })
                 -> p:(a, b) -> q:(a, b) -> r:(a, b)
                 -> { leqProd leqa leqb p q && leqProd leqa leqb q r ==> leqProd leqa leqb p r }
@-}
leqProdTrans :: Eq a
             => (a -> a -> Bool) -> (a -> a -> Proof) -> (a -> a -> a -> Proof)
             -> (b -> b -> Bool) -> (b -> b -> b -> Proof)
             -> (a, b) -> (a, b) -> (a, b) -> Proof
leqProdTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(x1, y1) q@(x2, y2) r@(x3, y3) =
    case x1 == x2 of
      True  -> case x2 == x3 of
        True  ->  (leqProd leqa leqb p q && leqProd leqa leqb q r)
              ==. (leqb y1 y2 && leqb y2 y3)
              ==. leqb y1 y3 ? leqbTrans y1 y2 y3
              ==. (if x1 == x3 then leqb y1 y3 else leqa x1 x3)
              ==. leqProd leqa leqb p r
              *** QED
        False ->  (leqProd leqa leqb p q && leqProd leqa leqb q r)
              ==. (leqb y1 y2 && leqa x2 x3)
              ==. leqa x1 x3
              ==. (if x1 == x3 then leqb y1 y3 else leqa x1 x3)
              ==. leqProd leqa leqb p r
              *** QED
      False -> case x2 == x3 of
        True  ->  (leqProd leqa leqb p q && leqProd leqa leqb q r)
              ==. (leqa x1 x2 && leqb y2 y3)
              ==. leqa x1 x3
              ==. (if x1 == x3 then leqb y1 y3 else leqa x1 x3)
              ==. leqProd leqa leqb p r
              *** QED
        False -> case x1 == x3 of
          True  ->  (leqProd leqa leqb p q && leqProd leqa leqb q r)
                ==. (leqa x1 x2 && leqa x2 x3)
                ==. (leqa x1 x2 && leqa x2 x1)
                ==. (x1 == x2) ? leqaAntisym x1 x2
                ==. leqb y1 y3
                ==. (if x1 == x3 then leqb y1 y3 else leqa x1 x3)
                *** QED
          False ->  (leqProd leqa leqb p q && leqProd leqa leqb q r)
                ==. (leqa x1 x2 && leqa x2 x3)
                ==. leqa x1 x3 ? leqaTrans x1 x2 x3
                ==. (if x1 == x3 then leqb y1 y3 else leqa x1 x3)
                ==. leqProd leqa leqb p r
                *** QED

{-@ leqProdTotal :: Eq a => leqa:(a -> a -> Bool) -> leqaTotal:(x:a -> y:a -> { leqa x y || leqa y x })
                 -> leqb:(b -> b -> Bool) -> leqbTotal:(x:b -> y:b -> { leqb x y || leqb y x })
                 -> p:(a, b) -> q:(a, b)
                 -> { leqProd leqa leqb p q || leqProd leqa leqb q p }
@-}
leqProdTotal :: Eq a => (a -> a -> Bool) -> (a -> a -> Proof)
             -> (b -> b -> Bool) -> (b -> b -> Proof)
             -> (a, b) -> (a, b) -> Proof
leqProdTotal leqa leqaTotal leqb leqbTotal p@(x1, y1) q@(x2, y2) =
      (leqProd leqa leqb p q || leqProd leqa leqb q p)
  ==. (if x1 == x2 then True else leqa x1 x2 || leqa x2 x1) ? leqbTotal y1 y2
  ==. (if x1 == x2 then True else True)                     ? leqaTotal x1 x2
  *** QED

vordProd :: VerifiedOrd a -> VerifiedOrd b -> VerifiedOrd (a, b)
vordProd (VerifiedOrd leqa leqaRefl leqaAntisym leqaTrans leqaTotal veqa) (VerifiedOrd leqb leqbRefl leqbAntisym leqbTrans leqbTotal veqb) =
  using (VEq veqa) $
    using (VEq veqb) $
      VerifiedOrd
        (leqProd leqa leqb)
        (leqProdRefl leqa leqaRefl leqb leqbRefl)
        (leqProdAntisym leqa leqaAntisym leqb leqbAntisym)
        (leqProdTrans leqa leqaAntisym leqaTrans leqb leqbTrans)
        (leqProdTotal leqa leqaTotal leqb leqbTotal)
        (veqProd veqa veqb)
