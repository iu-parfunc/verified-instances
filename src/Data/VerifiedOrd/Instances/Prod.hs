{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}

module Data.VerifiedOrd.Instances.Prod (vordProd) where

import Data.VerifiedEq
import Data.VerifiedOrd
import Data.VerifiedEq.Instances
import Data.VerifiableConstraint
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize leqProd @-}
leqProd :: (a -> a -> Bool) -> (b -> b -> Bool)
        -> (a, b) -> (a, b) -> Bool
leqProd leqa leqb p q =
  leqa (fst p) (fst q) && leqb (snd p) (snd q)

{-@ leqProdTotal :: leqa:(a -> a -> Bool) -> leqaTotal:(x:a -> y:a -> { Prop (leqa x y) || Prop (leqa y x) })
                 -> leqb:(b -> b -> Bool) -> leqbTotal:(x:b -> y:b -> { Prop (leqb x y) || Prop (leqb y x) })
                 -> p:(a, b) -> q:(a, b)
                 -> { leqProd leqa leqb p q || leqProd leqa leqb q p }
@-}
leqProdTotal :: (a -> a -> Bool) -> (a -> a -> Proof)
             -> (b -> b -> Bool) -> (b -> b -> Proof)
             -> (a, b) -> (a, b) -> Proof
leqProdTotal leqa leqaTotal leqb leqbTotal p@(x1, y1) q@(x2, y2) =
      (leqProd leqa leqb p q || leqProd leqa leqb q p)
  ==. ((leqa x1 x2 && leqb y1 y2) || (leqa x2 x1 && leqb y2 y1))
  ==. undefined
  ==. ((leqa x1 x2 || leqa x2 x1) && (leqb y1 y2 || leqb y2 y1))
  ==. (True && (leqb y1 y2 || leqb y2 y1)) ? leqaTotal x1 x2
  ==. (True && True)                       ? leqbTotal y1 y2
  ==. True
  *** QED

{-@ leqProdAntisym :: leqa:(a -> a -> Bool) -> leqaAntisym:(x:a -> y:a -> { Prop (leqa x y) && Prop (leqa y x) ==> x == y })
                   -> leqb:(b -> b -> Bool) -> leqbAntisym:(x:b -> y:b -> { Prop (leqb x y) && Prop (leqb y x) ==> x == y })
                   -> VerifiedEq a -> VerifiedEq b
                   -> p:(a, b) -> q:(a, b)
                   -> { leqProd leqa leqb p q && leqProd leqa leqb q p ==> q == p }
@-}
leqProdAntisym :: (a -> a -> Bool) -> (a -> a -> Proof)
               -> (b -> b -> Bool) -> (b -> b -> Proof)
               -> VerifiedEq a -> VerifiedEq b
               -> (a, b) -> (a, b) -> Proof
leqProdAntisym leqa leqaAntisym leqb leqbAntisym veqa veqb p@(x1, y1) q@(x2, y2) =
      using (VEq veqa)
    $ using (VEq veqb)
    $ (leqProd leqa leqb p q && leqProd leqa leqb q p)
  ==. ((leqa x1 x2 && leqb y1 y2) && (leqa x2 x1 && leqb y2 y1))
  ==. ((leqa x1 x2 && leqa x2 x1) && (leqb y1 y2 && leqb y2 y1))
  ==. (x1 == x2 && (leqb y1 y2 && leqb y2 y1)) ? leqaAntisym x1 x2
  ==. (x1 == x2 && y1 == y2)                   ? leqbAntisym y1 y2
  ==. p == q
  *** QED

{-@ leqProdTrans :: leqa:(a -> a -> Bool) -> leqaTrans:(x:a -> y:a -> z:a -> { Prop (leqa x y) && Prop (leqa y z) ==> Prop (leqa x z) })
                 -> leqb:(b -> b -> Bool) -> leqbTrans:(x:b -> y:b -> z:b -> { Prop (leqb x y) && Prop (leqb y z) ==> Prop (leqb x z) })
                 -> p:(a, b) -> q:(a, b) -> r:(a, b)
                 -> { leqProd leqa leqb p q && leqProd leqa leqb q r ==> leqProd leqa leqb p r }
@-}
leqProdTrans :: (a -> a -> Bool) -> (a -> a -> a -> Proof)
             -> (b -> b -> Bool) -> (b -> b -> b -> Proof)
             -> (a, b) -> (a, b) -> (a, b) -> Proof
leqProdTrans leqa leqaTrans leqb leqbTrans p@(x1, y1) q@(x2, y2) r@(x3, y3) =
      (leqProd leqa leqb p q && leqProd leqa leqb q r)
  ==. ((leqa x1 x2 && leqb y1 y2) && (leqa x2 x3 && leqb y2 y3))
  ==. ((leqa x1 x2 && leqa x2 x3) && (leqb y1 y2 && leqb y2 y3))
  ==. (leqa x1 x3 && (leqb y1 y2 && leqb y2 y3)) ? leqaTrans x1 x2 x3
  ==. (leqa x1 x3 && leqb y1 y3)                 ? leqbTrans y1 y2 y3
  ==. leqProd leqa leqb p r
  *** QED

vordProd :: VerifiedOrd a -> VerifiedOrd b -> VerifiedOrd (a, b)
vordProd (VerifiedOrd leqa leqaTotal leqaAntisym leqaTrans veqa) (VerifiedOrd leqb leqbTotal leqbAntisym leqbTrans veqb) =
  VerifiedOrd
    (leqProd leqa leqb)
    (leqProdTotal leqa leqaTotal leqb leqbTotal)
    (leqProdAntisym leqa leqaAntisym leqb leqbAntisym veqa veqb)
    (leqProdTrans leqa leqaTrans leqb leqbTrans)
    (veqProd veqa veqb)
