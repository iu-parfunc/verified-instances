{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--prune-unsorted"     @-}
{-@ LIQUID "--exactdc"            @-}
{-@ LIQUID "--trust-internals" @-}

module VerifiedAbelianMonoid where

import           Data.Iso
import           Language.Haskell.Liquid.ProofCombinators

{-@
data VerifiedAbelianMonoid a = VAM {
     empty  :: a
   , append :: a -> a -> a
   , commutes :: x:a -> y:a -> { append x y == append y x }
   , assoc    :: x:a -> y:a -> z:a
              -> { append x (append y z) == append (append x y) z}
   , lident   :: x:a -> { append empty x == x }
   , rident   :: x:a -> { append x empty == x }
   }
@-}
data VerifiedAbelianMonoid a = VAM {
    empty  :: a
  , append :: a -> a -> a
  , commutes :: a -> a -> Proof
  , assoc    :: a -> a -> a -> Proof
  , lident   :: a -> Proof
  , rident   :: a -> Proof
  }

-- {-@ emptyDouble :: {v:Double | emptyDouble == 0 } @-}
-- {-@ axiomatize emptyDouble @-}
-- emptyDouble :: Double
-- emptyDouble = 0
-- {-# INLINE emptyDouble #-}

{-@ axiomatize appendDouble @-}
appendDouble :: Double -> Double -> Double
appendDouble x y = x + y
{-# INLINE appendDouble #-}

{-@
commutesDouble :: x:Double -> y:Double
               -> { appendDouble x y == appendDouble y x }
@-}
commutesDouble :: Double -> Double -> Proof
commutesDouble x y
  =   appendDouble x y
  ==. x + y
  ==. y + x
  ==. appendDouble y x
  *** QED

{-@
assocDouble :: x:Double -> y:Double -> z:Double
            -> { appendDouble x (appendDouble y z) == appendDouble (appendDouble x y) z }
@-}
assocDouble :: Double -> Double -> Double -> Proof
assocDouble x y z
  =   appendDouble x (appendDouble y z)
  ==. x + (y + z)
  ==. (x + y) + z
  ==. appendDouble (appendDouble x y) z
  *** QED

{-@
lidentDouble :: x:Double -> { appendDouble 0 x == x }
@-}
lidentDouble :: Double -> Proof
lidentDouble x
  =   appendDouble 0 x
  ==. appendDouble 0 x
  ==. 0 + x
  ==. x
  *** QED

{-@
ridentDouble :: x:Double -> { appendDouble x 0 == x }
@-}
ridentDouble :: Double -> Proof
ridentDouble x
  =   appendDouble x 0
  ==. appendDouble x 0
  ==. x + 0
  ==. x
  *** QED

{-@ vamDouble :: VerifiedAbelianMonoid Double @-}
vamDouble :: VerifiedAbelianMonoid Double
vamDouble = VAM 0 appendDouble commutesDouble
                assocDouble lidentDouble ridentDouble

{-@ data Pair a b = Pair { fstOf :: a, sndOf :: b } @-}
data Pair a b = Pair { fstOf :: a, sndOf :: b }

{-@ axiomatize emptyPair @-}
emptyPair :: a -> b -> Pair a b
emptyPair x y = Pair x y
{-# INLINE emptyPair #-}

{-@ axiomatize appendPair @-}
appendPair :: (a -> a -> a) -> (b -> b -> b)
           -> Pair a b -> Pair a b -> Pair a b
appendPair appA appB p1 p2
  = Pair (appA (fstOf p1) (fstOf p2)) (appB (sndOf p1) (sndOf p2))
{-# INLINE appendPair #-}

{-@
commutesPair :: appA:(a -> a -> a)
             -> commutesA:(x:a -> y:a -> { appA x y == appA y x })
             -> appB:(b -> b -> b)
             -> commutesB:(x:b -> y:b -> { appB x y == appB y x })
             -> p1:Pair a b
             -> p2:Pair a b
             -> { appendPair appA appB p1 p2 == appendPair appA appB p2 p1 }
@-}
commutesPair :: (a -> a -> a) -> (a -> a -> Proof)
             -> (b -> b -> b) -> (b -> b -> Proof)
             -> Pair a b -> Pair a b -> Proof
commutesPair appA commutesA appB commutesB p1 p2
  =   appendPair appA appB p1 p2
  ==. Pair (appA (fstOf p1) (fstOf p2)) (appB (sndOf p1) (sndOf p2))
  ==. Pair (appA (fstOf p2) (fstOf p1)) (appB (sndOf p1) (sndOf p2)) ? commutesA (fstOf p1) (fstOf p2)
  ==. Pair (appA (fstOf p2) (fstOf p1)) (appB (sndOf p2) (sndOf p1)) ? commutesB (sndOf p1) (sndOf p2)
  ==. appendPair appA appB p2 p1
  *** QED

{-@
assocPair :: appA:(a -> a -> a)
          -> assocA:(x:a -> y:a -> z:a -> { appA x (appA y z) == appA (appA x y) z })
          -> appB:(b -> b -> b)
          -> assocB:(x:b -> y:b -> z:b -> { appB x (appB y z) == appB (appB x y) z })
          -> p1:Pair a b -> p2:Pair a b -> p3:Pair a b
          -> { appendPair appA appB p1 (appendPair appA appB p2 p3)
                == appendPair appA appB (appendPair appA appB p1 p2) p3 }
@-}
assocPair :: (a -> a -> a) -> (a -> a -> a -> Proof)
          -> (b -> b -> b) -> (b -> b -> b -> Proof)
          -> Pair a b -> Pair a b -> Pair a b -> Proof
assocPair appA assocA appB assocB p1@(Pair x1 y1) p2@(Pair x2 y2) p3@(Pair x3 y3)
  =   appendPair appA appB p1 (appendPair appA appB p2 p3)
  ==. appendPair appA appB p1 (Pair (appA x2 x3) (appB y2 y3))
  ==. Pair (appA x1 (appA x2 x3)) (appB y1 (appB y2 y3))
  ==. Pair (appA (appA x1 x2) x3) (appB y1 (appB y2 y3)) ? assocA x1 x2 x3
  ==. Pair (appA (appA x1 x2) x3) (appB (appB y1 y2) y3) ? assocB y1 y2 y3
  ==. appendPair appA appB (Pair (appA x1 x2) (appB y1 y2)) p3
  ==. appendPair appA appB (appendPair appA appB p1 p2) p3
  *** QED

{-@
lidentPair :: emptyA:a -> appA:(a -> a -> a)
           -> lidentA:(x:a -> { appA emptyA x == x })
           -> emptyB:b -> appB:(b -> b -> b)
           -> lidentB:(x:b -> { appB emptyB x == x })
           -> p:Pair a b
           -> { appendPair appA appB (emptyPair emptyA emptyB) p == p }
@-}
lidentPair :: a -> (a -> a -> a) -> (a -> Proof)
           -> b -> (b -> b -> b) -> (b -> Proof)
           -> Pair a b -> Proof
lidentPair emptyA appA lidentA emptyB appB lidentB p@(Pair x y)
  =   appendPair appA appB (emptyPair emptyA emptyB) p
  ==. appendPair appA appB (Pair emptyA emptyB) p
  ==. Pair (appA (fstOf (Pair emptyA emptyB)) x) (appB (sndOf (Pair emptyA emptyB)) y)
  ==. Pair (appA emptyA x) (appB emptyB y)
  ==. Pair x (appB emptyB y) ? lidentA x
  ==. Pair x y               ? lidentB y
  ==. p
  *** QED

{-@
ridentPair :: emptyA:a -> appA:(a -> a -> a)
           -> lidentA:(x:a -> { appA x emptyA == x })
           -> emptyB:b -> appB:(b -> b -> b)
           -> lidentB:(x:b -> { appB x emptyB == x })
           -> p:Pair a b
           -> { appendPair appA appB p (emptyPair emptyA emptyB) == p }
@-}
ridentPair :: a -> (a -> a -> a) -> (a -> Proof)
           -> b -> (b -> b -> b) -> (b -> Proof)
           -> Pair a b -> Proof
ridentPair emptyA appA ridentA emptyB appB ridentB p@(Pair x y)
  =   appendPair appA appB p (emptyPair emptyA emptyB)
  ==. appendPair appA appB p (Pair emptyA emptyB)
  ==. Pair (appA x (fstOf (Pair emptyA emptyB))) (appB y (sndOf (Pair emptyA emptyB)))
  ==. Pair (appA x emptyA) (appB y emptyB)
  ==. Pair x (appB y emptyB) ? ridentA x
  ==. Pair x y               ? ridentB y
  ==. p
  *** QED

{-@ vamPair :: VerifiedAbelianMonoid a -> VerifiedAbelianMonoid b
            -> VerifiedAbelianMonoid (Pair a b)
@-}
vamPair :: VerifiedAbelianMonoid a -> VerifiedAbelianMonoid b
        -> VerifiedAbelianMonoid (Pair a b)
vamPair (VAM emptyA appendA commutesA assocA lidentA ridentA)
        (VAM emptyB appendB commutesB assocB lidentB ridentB)
  = VAM (emptyPair emptyA emptyB)
        (appendPair appendA appendB)
        (commutesPair appendA commutesA appendB commutesB)
        (assocPair appendA assocA appendB assocB)
        (lidentPair emptyA appendA lidentA emptyB appendB lidentB)
        (ridentPair emptyA appendA ridentA emptyB appendB ridentB)

{-@ axiomatize vamIsoEmpty @-}
vamIsoEmpty :: (a -> b) -> a -> b
vamIsoEmpty t emp = t emp
{-# INLINE vamIsoEmpty #-}

{-@ axiomatize vamIsoAppend @-}
vamIsoAppend :: (a -> b) -> (b -> a) -> (a -> a -> a) -> b -> b -> b
vamIsoAppend t f app x y = t (app (f x) (f y))
{-# INLINE vamIsoAppend #-}

{-@
vamIsoCommutes :: t:(a -> b) -> f:(b -> a) -> appA:(a -> a -> a)
               -> commA:(xa:a -> ya:a -> { appA xa ya == appA ya xa })
               -> xb:b -> yb:b
               -> { vamIsoAppend t f appA xb yb == vamIsoAppend t f appA yb xb }
@-}
vamIsoCommutes :: (a -> b) -> (b -> a) -> (a -> a -> a) -> (a -> a -> Proof)
               -> b -> b -> Proof
vamIsoCommutes t f appA commA xb yb
  =   vamIsoAppend t f appA xb yb
  ==. t (appA (f xb) (f yb))
  ==. t (appA (f yb) (f xb)) ? commA (f xb) (f yb)
  ==. vamIsoAppend t f appA yb xb
  *** QED

{-@
vamIsoAssoc :: t:(a -> b) -> f:(b -> a) -> appA:(a -> a -> a)
            -> assocA:(xa:a -> ya:a -> za:a
                            -> { appA xa (appA ya za) == appA (appA xa ya) za })
            -> fot:(x:a -> { f (t x) == x })
            -> xb:b -> yb:b -> zb:b
            -> { vamIsoAppend t f appA xb (vamIsoAppend t f appA yb zb)
                 == vamIsoAppend t f appA (vamIsoAppend t f appA xb yb) zb }
@-}
vamIsoAssoc :: (a -> b) -> (b -> a) -> (a -> a -> a) -> (a -> a -> a -> Proof)
            -> (a -> Proof) -> b -> b -> b -> Proof
vamIsoAssoc t f appA assocA fot xb yb zb
  =   vamIsoAppend t f appA xb (vamIsoAppend t f appA yb zb)
  ==. vamIsoAppend t f appA xb (t (appA (f yb) (f zb)))
  ==. t (appA (f xb) (f (t (appA (f yb) (f zb)))))
  ==. t (appA (f xb) (appA (f yb) (f zb))) ? fot (appA (f yb) (f zb))
  ==. t (appA (appA (f xb) (f yb)) (f zb)) ? assocA (f xb) (f yb) (f zb)
  ==. t (appA (f (t (appA (f xb) (f yb)))) (f zb)) ? fot (appA (f xb) (f yb))
  ==. vamIsoAppend t f appA (t (appA (f xb) (f yb))) zb
  ==. vamIsoAppend t f appA (vamIsoAppend t f appA xb yb) zb
  *** QED

{-@
vamIsoLident :: t:(a -> b) -> f:(b -> a) -> empA:a -> appA:(a -> a -> a)
             -> lidentA:(x:a -> { appA empA x == x })
             -> tof:(x:b -> { t (f x) == x })
             -> fot:(x:a -> { f (t x) == x })
             -> x:b -> { vamIsoAppend t f appA (vamIsoEmpty t empA) x == x }
@-}
vamIsoLident :: (a -> b) -> (b -> a) -> a -> (a -> a -> a) -> (a -> Proof)
             -> (b -> Proof) -> (a -> Proof)
             -> b -> Proof
vamIsoLident t f empA appA lidentA tof fot x
  =   vamIsoAppend t f appA (vamIsoEmpty t empA) x
  ==. t (appA (f (vamIsoEmpty t empA)) (f x))
  ==. t (appA (f (t empA)) (f x))
  ==. t (appA empA (f x)) ? fot empA
  ==. t (f x) ? lidentA (f x)
  ==. x ? tof x
  *** QED

{-@
vamIsoRident :: t:(a -> b) -> f:(b -> a) -> empA:a -> appA:(a -> a -> a)
             -> ridentA:(x:a -> { appA x empA == x })
             -> tof:(x:b -> { t (f x) == x })
             -> fot:(x:a -> { f (t x) == x })
             -> x:b -> { vamIsoAppend t f appA x (vamIsoEmpty t empA) == x }
@-}
vamIsoRident :: (a -> b) -> (b -> a) -> a -> (a -> a -> a) -> (a -> Proof)
             -> (b -> Proof) -> (a -> Proof)
             -> b -> Proof
vamIsoRident t f empA appA ridentA tof fot x
  =   vamIsoAppend t f appA x (vamIsoEmpty t empA)
  ==. t (appA (f x) (f (vamIsoEmpty t empA)))
  ==. t (appA (f x) (f (t empA)))
  ==. t (appA (f x) empA) ? fot empA
  ==. t (f x) ? ridentA (f x)
  ==. x ? tof x
  *** QED

{-@
vamIso :: Iso a b -> VerifiedAbelianMonoid a -> VerifiedAbelianMonoid b
@-}
vamIso :: Iso a b -> VerifiedAbelianMonoid a -> VerifiedAbelianMonoid b
vamIso iso@(Iso t f tof fot) (VAM emp app comm asso liden riden)
 = VAM (vamIsoEmpty t emp)
       (vamIsoAppend t f app)
       (vamIsoCommutes t f app comm)
       (vamIsoAssoc t f app asso fot)
       (vamIsoLident t f emp app liden tof fot)
       (vamIsoRident t f emp app riden tof fot)
