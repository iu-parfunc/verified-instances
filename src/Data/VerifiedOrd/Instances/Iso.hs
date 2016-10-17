{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}

module Data.VerifiedOrd.Instances.Iso (vordIso) where

import Data.Iso
import Data.VerifiedEq
import Data.VerifiedOrd
import Data.VerifiableConstraint
import Data.VerifiedEq.Instances
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize leqFrom @-}
leqFrom :: (a -> a -> Bool)
        -> (b -> a)
        -> (b -> b -> Bool)
leqFrom leqa from x y = leqa (from x) (from y)

{-@ leqFromTotal :: leqa:(a -> a -> Bool) -> leqaTotal:(x:a -> y:a -> { Prop (leqa x y) || Prop (leqa y x) })
                 -> from:(b -> a) -> x:b -> y:b -> { leqFrom leqa from x y || leqFrom leqa from y x }
@-}
leqFromTotal :: (a -> a -> Bool) -> (a -> a -> Proof)
             -> (b -> a) -> b -> b -> Proof
leqFromTotal leqa leqaTotal from x y =
      (leqFrom leqa from x y || leqFrom leqa from y x)
  ==. (leqa (from x) (from y) || leqa (from y) (from x))
  ==. True ? leqaTotal (from x) (from y)
  ==. leqFrom leqa from y x
  *** QED

{-@ leqFromAntisym :: leqa:(a -> a -> Bool)
                   -> leqaAntisym:(x:a -> y:a -> { Prop (leqa x y) && Prop (leqa y x) ==> x == y })
                   -> VerifiedEq a
                   -> from:(b -> a) -> to:(a -> b) -> tof:(x:b -> { to (from x) == x })
                   -> x:b -> y:b -> { leqFrom leqa from x y && leqFrom leqa from y x ==> x == y }
@-}
leqFromAntisym :: (a -> a -> Bool) -> (a -> a -> Proof)
               -> VerifiedEq a
               -> (b -> a) -> (a -> b) -> (b -> Proof)
               -> b -> b -> Proof
leqFromAntisym leqa leqaAntisym veqa from to tof x y =
      using (VEq veqa)
    $ using (VEq $ veqContra from veqa)
    $ (leqFrom leqa from x y && leqFrom leqa from y x)
  ==. (leqa (from x) (from y) && leqa (from y) (from x))
  ==. from x == from y ? leqaAntisym (from x) (from y)
  ==. to (from x) == to (from y)
  ==. x == to (from y) ? tof x
  ==. x == y ? tof y
  *** QED

{-@ leqFromTrans :: leqa:(a -> a -> Bool)
                 -> leqaTrans:(x:a -> y:a -> z:a -> { Prop (leqa x y) && Prop (leqa y z) ==> Prop (leqa x z) })
                 -> from:(b -> a)
                 -> x:b -> y:b -> z:b
                 -> { leqFrom leqa from x y && leqFrom leqa from y z ==> leqFrom leqa from x z }
@-}
leqFromTrans :: (a -> a -> Bool) -> (a -> a -> a -> Proof)
             -> (b -> a)
             -> b -> b -> b -> Proof
leqFromTrans leqa leqaTrans from x y z =
      (leqFrom leqa from x y && leqFrom leqa from y z)
  ==. (leqa (from x) (from y) && leqa (from y) (from z))
  ==. leqa (from x) (from z) ? leqaTrans (from x) (from y) (from z)
  ==. leqFrom leqa from x z
  *** QED

vordIso :: Iso a b -> VerifiedOrd a -> VerifiedOrd b
vordIso (Iso to from tof fot) (VerifiedOrd leqa leqaTotal leqaAntisym leqaTrans veqa) =
  VerifiedOrd
    (leqFrom leqa from)
    (leqFromTotal leqa leqaTotal from)
    (leqFromAntisym leqa leqaAntisym veqa from to tof)
    (leqFromTrans leqa leqaTrans from)
    (veqContra from veqa)
