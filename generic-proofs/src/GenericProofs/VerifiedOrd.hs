{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--noadt"              @-}

module GenericProofs.VerifiedOrd (VerifiedOrd(..), {-vordEq,-} eqCompare, leqFrom, vordIso) where

import GenericProofs.Iso
import Language.Haskell.Liquid.ProofCombinators

{-@ data VerifiedOrd a = VerifiedOrd {
      leq :: (a -> a -> Bool)
    , refl :: (x:a -> { leq x x })
    , antisym :: (x:a -> y:a -> { leq x y && leq y x ==> x == y })
    , trans :: (x:a -> y:a -> z:a -> { leq x y && leq y z ==> leq x z })
    , total :: (x:a -> y:a -> { leq x y || leq y x })
    }
@-}
data VerifiedOrd a = VerifiedOrd {
    leq     :: a -> a -> Bool
  , refl    :: a -> Proof
  , antisym :: a -> a -> Proof
  , trans   :: a -> a -> a -> Proof
  , total   :: a -> a -> Proof
  }

{-
-- | Test for equality using 'VerifiedOrd'.
{-@ axiomatize vordEq @-}
vordEq :: VerifiedOrd a -> a -> a -> Bool
vordEq (VerifiedOrd { leq = leq' }) = eqCompare leq'
{-# INLINE vordEq #-}
-}

-- | Test for equality using a 'leq' function.
{-@ axiomatize eqCompare @-}
eqCompare :: (a -> a -> Bool) -> a -> a -> Bool
eqCompare cmp x y = cmp x y && cmp y x
{-# INLINE eqCompare #-}

{-@ axiomatize leqFrom @-}
leqFrom :: (a -> a -> Bool)
        -> (b -> a)
        -> (b -> b -> Bool)
leqFrom leqa from x y = leqa (from x) (from y)
{-# INLINE leqFrom #-}

{-@ leqFromRefl :: leqa:(a -> a -> Bool) -> leqaRefl:(x:a -> { leqa x x })
                -> from:(b -> a)
                -> x:b -> { leqFrom leqa from x x }
@-}
leqFromRefl :: (a -> a -> Bool) -> (a -> Proof)
            -> (b -> a)
            -> b -> Proof
leqFromRefl leqa leqaRefl from x =
      leqFrom leqa from x x
  ==. leqa (from x) (from x)
  ==. True ? leqaRefl (from x)
  *** QED

{-@ leqFromAntisym :: leqa:(a -> a -> Bool)
                   -> leqaAntisym:(x:a -> y:a -> { leqa x y && leqa y x ==> x == y })
                   -> from:(b -> a) -> fromInj:(x:b -> y:b -> { from x == from y ==> x == y })
                   -> x:b -> y:b -> { leqFrom leqa from x y && leqFrom leqa from y x ==> x == y }
@-}
leqFromAntisym :: (Eq a, Eq b)
               => (a -> a -> Bool) -> (a -> a -> Proof)
               -> (b -> a) -> (b -> b -> Proof)
               -> b -> b -> Proof
leqFromAntisym leqa leqaAntisym from fromInj x y
  =   (leqFrom leqa from x y && leqFrom leqa from y x)
  ==. (leqa (from x) (from y) && leqa (from y) (from x))
  ==. from x == from y ? leqaAntisym (from x) (from y)
  ==. x == y           ? fromInj x y
  *** QED

{-@ leqFromTrans :: leqa:(a -> a -> Bool)
                 -> leqaTrans:(x:a -> y:a -> z:a -> { leqa x y && leqa y z ==> leqa x z })
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

{-@ leqFromTotal :: leqa:(a -> a -> Bool) -> leqaTotal:(x:a -> y:a -> { leqa x y || leqa y x })
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

vordIso :: (Eq a, Eq b) => Iso a b -> VerifiedOrd a -> VerifiedOrd b
vordIso (Iso to from tof fot) (VerifiedOrd leqa leqaRefl leqaAntisym leqaTrans leqaTotal) =
    VerifiedOrd
        (leqFrom leqa from)
        (leqFromRefl leqa leqaRefl from)
        (leqFromAntisym leqa leqaAntisym from (fromInj to from tof))
        (leqFromTrans leqa leqaTrans from)
        (leqFromTotal leqa leqaTotal from)
