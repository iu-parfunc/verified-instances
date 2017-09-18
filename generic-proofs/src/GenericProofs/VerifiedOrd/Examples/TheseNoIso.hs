{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}

module GenericProofs.VerifiedOrd.Examples.TheseNoIso
  ( These(..)
  , leqThese
  , vordThese
  ) where

import Language.Haskell.Liquid.ProofCombinators

import GenericProofs.VerifiedOrd

{-@ data These = This a | That b | These { a :: a, b :: b } @-}
data These a b = This a | That b | These a b deriving (Eq)

{-@ axiomatize leqThese @-}
leqThese :: Eq a => (a -> a -> Bool) -> (b -> b -> Bool)
         -> These a b -> These a b -> Bool
leqThese leqa leqb (This x)      (This y)      = leqa x y
leqThese leqa leqb (This x)      (That _)      = True
leqThese leqa leqb (This x)      (These _ _)   = True
leqThese leqa leqb (That x)      (This _)      = False
leqThese leqa leqb (That x)      (That y)      = leqb x y
leqThese leqa leqb (That x)      (These _ _)   = True
leqThese leqa leqb (These x1 y1) (This _)      = False
leqThese leqa leqb (These x1 y1) (That _)      = False
leqThese leqa leqb (These x1 y1) (These x2 y2) = if x1 == x2 then leqb y1 y2 else leqa x1 x2

{-@ leqTheseRefl :: leqa:(a -> a -> Bool) -> leqaRefl:(x:a -> {leqa x x})
                 -> leqb:(b -> b -> Bool) -> leqbRefl:(y:b -> {leqb y y})
                 -> p:These a b -> { leqThese leqa leqb p p }
@-}
leqTheseRefl :: Eq a
             => (a -> a -> Bool) -> (a -> Proof)
             -> (b -> b -> Bool) -> (b -> Proof)
             -> These a b -> Proof
leqTheseRefl leqa leqaRefl leqb leqbRefl p@(This x) =
      leqThese leqa leqb p p
  ==. leqa x x
  ==. True ? leqaRefl x
  *** QED
leqTheseRefl leqa leqaRefl leqb leqbRefl p@(That y) =
      leqThese leqa leqb p p
  ==. leqb y y
  ==. True ? leqbRefl y
  *** QED
leqTheseRefl leqa leqaRefl leqb leqbRefl p@(These x y) =
      leqThese leqa leqb p p
  ==. (if x == x then leqb y y else leqa x x)
  ==. leqb y y
  ==. True ? leqbRefl y
  *** QED

{-@ leqTheseAntisym :: leqa:(a -> a -> Bool) -> leqaAntisym:(x:a -> y:a -> {leqa x y && leqa y x ==> x == y})
                    -> leqb:(b -> b -> Bool) -> leqbAntisym:(x:b -> y:b -> {leqb x y && leqb y x ==> x == y})
                    -> p:These a b -> q:These a b -> {leqThese leqa leqb p q && leqThese leqa leqb q p ==> p == q}
@-}
leqTheseAntisym :: (Eq a, Eq b)
                => (a -> a -> Bool) -> (a -> a -> Proof)
                -> (b -> b -> Bool) -> (b -> b -> Proof)
                -> These a b -> These a b -> Proof
leqTheseAntisym leqa leqaAntisym leqb leqbAntisym p@(This x)      q@(This y)      =
      (leqThese leqa leqb p q && leqThese leqa leqb q p)
  ==. (leqa x y && leqa y x)
  ==. True ? leqaAntisym x y
  *** QED
leqTheseAntisym leqa leqaAntisym leqb leqbAntisym p@(This x)      q@(That _)      =
      (leqThese leqa leqb p q && leqThese leqa leqb q p)
  ==. (True && False)
  *** QED
leqTheseAntisym leqa leqaAntisym leqb leqbAntisym p@(This x)      q@(These _ _)   =
      (leqThese leqa leqb p q && leqThese leqa leqb q p)
  ==. (True && False)
  *** QED
leqTheseAntisym leqa leqaAntisym leqb leqbAntisym p@(That x)      q@(This _)      =
      (leqThese leqa leqb p q && leqThese leqa leqb q p)
  ==. (False && True)
  *** QED
leqTheseAntisym leqa leqaAntisym leqb leqbAntisym p@(That x)      q@(That y)      =
      (leqThese leqa leqb p q && leqThese leqa leqb q p)
  ==. (leqb x y && leqb y x)
  ==. True ? leqbAntisym x y
  *** QED
leqTheseAntisym leqa leqaAntisym leqb leqbAntisym p@(That x)      q@(These _ _)   =
      (leqThese leqa leqb p q && leqThese leqa leqb q p)
  ==. (True && False)
  *** QED
leqTheseAntisym leqa leqaAntisym leqb leqbAntisym p@(These x1 y1) q@(This _)      =
      (leqThese leqa leqb p q && leqThese leqa leqb q p)
  ==. (False && True)
  *** QED
leqTheseAntisym leqa leqaAntisym leqb leqbAntisym p@(These x1 y1) q@(That _)      =
      (leqThese leqa leqb p q && leqThese leqa leqb q p)
  ==. (False && True)
  *** QED
leqTheseAntisym leqa leqaAntisym leqb leqbAntisym p@(These x1 y1) q@(These x2 y2) =
      (leqThese leqa leqb p q && leqThese leqa leqb q p)
  ==. ((if x1 == x2 then leqb y1 y2 else leqa x1 x2) && (if x2 == x1 then leqb y2 y1 else leqa x2 x1))
  ==. (if x1 == x2 then leqb y1 y2 && leqb y2 y1 else leqa x1 x2 && leqa x2 x1)
  ==. (if x1 == x2 then y1 == y2 else leqa x1 x2 && leqa x2 x1) ? leqbAntisym y1 y2
  ==. (if x1 == x2 then y1 == y2 else x1 == x2) ? leqaAntisym x1 x2
  ==. (x1 == x2 && y1 == y2)
  ==. p == q
  *** QED

{-@ leqTheseTrans :: leqa:(a -> a -> Bool) -> leqaAntisym:(x:a -> y:a -> {leqa x y && leqa y x ==> x == y}) -> leqaTrans:(x:a -> y:a -> z:a -> {leqa x y && leqa y z ==> leqa x z})
                  -> leqb:(b -> b -> Bool) -> leqbTrbns:(x:b -> y:b -> z:b -> {leqb x y && leqb y z ==> leqb x z})
                  -> p:These a b -> q:These a b -> r:These a b -> {leqThese leqa leqb p q && leqThese leqa leqb q r ==> leqThese leqa leqb p r}
@-}
leqTheseTrans :: Eq a => (a -> a -> Bool) -> (a -> a -> Proof) -> (a -> a -> a -> Proof)
              -> (b -> b -> Bool) -> (b -> b -> b -> Proof)
              -> These a b -> These a b -> These a b -> Proof
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(This x)    q@(This y)    r@(This z)    =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (leqa x y && leqa y z)
  ==. leqa x z ? leqaTrans x y z
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(This x)    q@(This y)    r@(That z)    =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (leqa x y && True)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(This x)    q@(This y)    r@(These z u) =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (leqa x y && True)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(This x)    q@(That y)    r@(This z)    =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (True && False)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(This x)    q@(That y)    r@(That z)    =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (True && leqb y z)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(This x)    q@(That y)    r@(These z u) =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (True && True)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(This x)    q@(These y z) r@(This u)    =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (True && False)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(This x)    q@(These y z) r@(That u)    =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (True && False)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(This x)    q@(These y z) r@(These u v) =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (True && (if y == u then leqb z v else leqa y u))
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(That x)    q@(This y)    r@(This z)    =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (False && leqa y z)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(That x)    q@(This y)    r@(That z)    =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (False && True)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(That x)    q@(This y)    r@(These z u) =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (False && True)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(That x)    q@(That y)    r@(This z)    =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (leqb x y && False)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(That x)    q@(That y)    r@(That z)    =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (leqb x y && leqb y z)
  ==. leqb x z ? leqbTrans x y z
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(That x)    q@(That y)    r@(These z u) =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (leqb x y && True)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(That x)    q@(These y z) r@(This u)    =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (True && False)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(That x)    q@(These y z) r@(That u)    =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (True && False)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(That x)    q@(These y z) r@(These u v) =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (True && (if y == u then leqb z v else leqa y u))
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(These x y) q@(This z)    r@(This u)    =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (False && leqa z u)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(These x y) q@(This z)    r@(That u)    =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (False && True)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(These x y) q@(This z)    r@(These u v) =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (False && True)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(These x y) q@(That z)    r@(This u)    =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (False && False)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(These x y) q@(That z)    r@(That u)    =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (False && leqb z u)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(These x y) q@(That z)    r@(These u v) =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. (False && True)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(These x y) q@(These z u) r@(This v)    =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. ((if x == z then leqb y u else leqa x z) && False)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(These x y) q@(These z u) r@(That v)    =
      (leqThese leqa leqb p q && leqThese leqa leqb q r)
  ==. ((if x == z then leqb y u else leqa x z) && False)
  ==. leqThese leqa leqb p r
  *** QED
leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans p@(These x y) q@(These z u) r@(These v w) =
    case x == z of
      True  -> case z == v of
        True  ->  (leqThese leqa leqb p q && leqThese leqa leqb q r)
              ==. (leqb y u && leqb u w)
              ==. leqb y w ? leqbTrans y u w
              ==. (if x == v then leqb y w else leqa x v)
              ==. leqThese leqa leqb p r
              *** QED
        False ->  (leqThese leqa leqb p q && leqThese leqa leqb q r)
              ==. (leqb y u && leqa z v)
              ==. leqa x v
              ==. (if x == v then leqb y w else leqa x v)
              ==. leqThese leqa leqb p r
              *** QED
      False -> case z == v of
        True  ->  (leqThese leqa leqb p q && leqThese leqa leqb q r)
              ==. (leqa x z && leqb u w)
              ==. leqa x v
              ==. (if x == v then leqb y w else leqa x v)
              ==. leqThese leqa leqb p r
              *** QED
        False -> case x == v of
          True  ->  (leqThese leqa leqb p q && leqThese leqa leqb q r)
                ==. (leqa x z && leqa z v)
                ==. (leqa x z && leqa z x)
                ==. (x == z) ? leqaAntisym x z
                ==. leqb y w
                ==. (if x == v then leqb y w else leqa x v)
                *** QED
          False ->  (leqThese leqa leqb p q && leqThese leqa leqb q r)
                ==. (leqa x z && leqa z v)
                ==. leqa x v ? leqaTrans x z v
                ==. (if x == v then leqb y w else leqa x v)
                ==. leqThese leqa leqb p r
                *** QED

{-@ leqTheseTotal :: leqa:(a -> a -> Bool) -> leqaTotal:(x:a -> y:a -> {leqa x y || leqa y x})
                  -> leqb:(b -> b -> Bool) -> leqbTotal:(x:b -> y:b -> {leqb x y || leqb y x})
                  -> p:These a b -> q:These a b -> {leqThese leqa leqb p q || leqThese leqa leqb q p}
@-}
leqTheseTotal :: Eq a => (a -> a -> Bool) -> (a -> a -> Proof)
              -> (b -> b -> Bool) -> (b -> b -> Proof)
              -> These a b -> These a b -> Proof
leqTheseTotal leqa leqaTotal leqb leqbTotal p@(This x)      q@(This y)      =
      (leqThese leqa leqb p q || leqThese leqa leqb q p)
  ==. (leqa x y || leqa y x)
  ==. True ? leqaTotal x y
  *** QED
leqTheseTotal leqa leqaTotal leqb leqbTotal p@(This x)      q@(That _)      =
      (leqThese leqa leqb p q || leqThese leqa leqb q p)
  ==. (True || False)
  *** QED
leqTheseTotal leqa leqaTotal leqb leqbTotal p@(This x)      q@(These _ _)   =
      (leqThese leqa leqb p q || leqThese leqa leqb q p)
  ==. (True || False)
  *** QED
leqTheseTotal leqa leqaTotal leqb leqbTotal p@(That x)      q@(This _)      =
      (leqThese leqa leqb p q || leqThese leqa leqb q p)
  ==. (False || True)
  *** QED
leqTheseTotal leqa leqaTotal leqb leqbTotal p@(That x)      q@(That y)      =
      (leqThese leqa leqb p q || leqThese leqa leqb q p)
  ==. (leqb x y || leqb y x)
  ==. True ? leqbTotal x y
  *** QED
leqTheseTotal leqa leqaTotal leqb leqbTotal p@(That x)      q@(These _ _)   =
      (leqThese leqa leqb p q || leqThese leqa leqb q p)
  ==. (True || False)
  *** QED
leqTheseTotal leqa leqaTotal leqb leqbTotal p@(These x1 y1) q@(This _)      =
      (leqThese leqa leqb p q || leqThese leqa leqb q p)
  ==. (False || True)
  *** QED
leqTheseTotal leqa leqaTotal leqb leqbTotal p@(These x1 y1) q@(That _)      =
      (leqThese leqa leqb p q || leqThese leqa leqb q p)
  ==. (False || True)
  *** QED
leqTheseTotal leqa leqaTotal leqb leqbTotal p@(These x1 y1) q@(These x2 y2) =
      (leqThese leqa leqb p q || leqThese leqa leqb q p)
  ==. ((if x1 == x2 then leqb y1 y2 else leqa x1 x2) || (if x2 == x1 then leqb y2 y1 else leqa x2 x1))
  ==. (if x1 == x2 then (leqb y1 y2 || leqb y2 y1) else (leqa x1 x2 || leqa x2 x1))
  ==. (if x1 == x2 then True else (leqa x1 x2 || leqa x2 x1)) ? leqbTotal y1 y2
  ==. (if x1 == x2 then True else True) ? leqaTotal x1 x2
  ==. True
  *** QED

vordThese :: (Eq a, Eq b) => VerifiedOrd a -> VerifiedOrd b -> VerifiedOrd (These a b)
vordThese (VerifiedOrd leqa leqaRefl leqaAntisym leqaTrans leqaTotal) (VerifiedOrd leqb leqbRefl leqbAntisym leqbTrans leqbTotal) =
    VerifiedOrd
        (leqThese leqa leqb)
        (leqTheseRefl leqa leqaRefl leqb leqbRefl)
        (leqTheseAntisym leqa leqaAntisym leqb leqbAntisym)
        (leqTheseTrans leqa leqaAntisym leqaTrans leqb leqbTrans)
        (leqTheseTotal leqa leqaTotal leqb leqbTotal)
