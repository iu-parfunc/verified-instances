{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--totality"       @-}
{-@ LIQUID "--exactdc"        @-}
{-# LANGUAGE EmptyCase     #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}
module GenericProofs.VerifiedFunctor.Generics where

import GenericProofs.VerifiedFunctor
import Generics.Deriving.Newtypeless.Base.Internal
import Language.Haskell.Liquid.ProofCombinators

{-
{-@ measure fmapV1 :: (p -> q) -> V1 p -> V1 q @-}
fmapV1 :: (p -> q) -> V1 p -> V1 q
fmapV1 _ x = absurd x

absurd :: V1 p -> a
absurd x = case x of {}

{-@ fmapV1Id :: x:V1 p
             -> { fmapV1 _identity x == x }
@-}
fmapV1Id :: V1 p -> Proof
fmapV1Id x
 =   fmapV1 _identity x
 ==. absurd x
 ==. x
 *** QED

{-@ fmapV1Compose :: f:(q -> r)
                  -> g:(p -> q)
                  -> x:V1 p
                  -> { fmapV1 (_compose f g) x == _compose (fmapV1 f) (fmapV1 g) x }
@-}
fmapV1Compose :: (q -> r) -> (p -> q)
              -> V1 p -> Proof
fmapV1Compose f g x
  =   fmapV1 (_compose f g) x
  ==. absurd x
  ==. fmapV1 f (fmapV1 g x)
  ==. _compose (fmapV1 f) (fmapV1 g) x
  *** QED

vfunctorV1 :: VerifiedFunctor V1
vfunctorV1 = VerifiedFunctor fmapV1 fmapV1Id fmapV1Compose
-}

{-@ axiomatize fmapU1 @-}
fmapU1 :: (p -> q) -> U1 p -> U1 q
fmapU1 _ _ = U1

{-@ fmapU1Id :: x:U1 p
             -> { fmapU1 _identity x == x }
@-}
fmapU1Id :: U1 p -> Proof
fmapU1Id U1
  =   fmapU1 _identity U1
  ==. U1
  *** QED

{-@ fmapU1Compose :: f:(q -> r)
                  -> g:(p -> q)
                  -> x:U1 p
                  -> { fmapU1 (_compose f g) x == _compose (fmapU1 f) (fmapU1 g) x }
@-}
fmapU1Compose :: (q -> r) -> (p -> q)
              -> U1 p -> Proof
fmapU1Compose f g x
  =   fmapU1 (_compose f g) x
  ==. U1
  ==. fmapU1 f (fmapU1 g x)
  ==. _compose (fmapU1 f) (fmapU1 g) x
  *** QED

vfunctorU1 :: VerifiedFunctor U1
vfunctorU1 = VerifiedFunctor fmapU1 fmapU1Id fmapU1Compose

{-@ axiomatize fmapPar1 @-}
fmapPar1 :: (p -> q) -> Par1 p -> Par1 q
fmapPar1 f (Par1 p) = Par1 (f p)

{-@ fmapPar1Id :: x:Par1 p
               -> { fmapPar1 _identity x == x }
@-}
fmapPar1Id :: Par1 p -> Proof
fmapPar1Id par@(Par1 p)
  =   fmapPar1 _identity par
  ==. Par1 (_identity p)
  ==. Par1 p
  ==. par
  *** QED

{-@ fmapPar1Compose :: f:(q -> r)
                    -> g:(p -> q)
                    -> x:Par1 p
                    -> { fmapPar1 (_compose f g) x == _compose (fmapPar1 f) (fmapPar1 g) x } @-}
fmapPar1Compose :: (q -> r) -> (p -> q)
                -> Par1 p -> Proof
fmapPar1Compose f g x@(Par1 p)
  =   fmapPar1 (_compose f g) x
  ==. fmapPar1 (_compose f g) (Par1 p)
  ==. Par1 (_compose f g p)
  ==. Par1 (f (g p))
  ==. fmapPar1 f (Par1 (g p))
  ==. fmapPar1 f (fmapPar1 g (Par1 p))
  ==. _compose (fmapPar1 f) (fmapPar1 g) (Par1 p)
  ==. _compose (fmapPar1 f) (fmapPar1 g) x
  *** QED

vfunctorPar1 :: VerifiedFunctor Par1
vfunctorPar1 = VerifiedFunctor fmapPar1 fmapPar1Id fmapPar1Compose

{-
{-@ axiomatize fmapRec1 @-}
fmapRec1 :: (forall a b. (a -> b) -> f a -> f b)
         -> (p -> q) -> Rec1 f p -> Rec1 f q
fmapRec1 fmapF f (Rec1 fp) = Rec1 (fmapF f fp)

{-
{-@ fmapRec1Id :: fmapF:(forall a b. (a -> b) -> f a -> f b)
               -> fmapFId:(forall a. y:(f a) -> { fmapF _identity y == y })
               -> r:Rec1 f p
               -> { fmapRec1 fmapF _identity r == r }
@-}
-}
fmapRec1Id :: (forall a b. (a -> b) -> f a -> f b)
           -> (forall a. f a -> Proof)
           -> Rec1 f p -> Proof
fmapRec1Id fmapF fmapFId r@(Rec1 fp)
  =   fmapRec1 fmapF _identity r
  ==. Rec1 (fmapF _identity fp)
  ==. Rec1 (_identity fp) ? fmapFId fp
  ==. Rec1 fp
  ==. r
  *** QED

{-
{-@ fmapRec1Compose :: fmapF:(forall a b. (a -> b) -> f a -> f b)
                    -> fmapFId:(forall a b c. f':(b -> c) -> g':(a -> b) -> y:(f a) -> { fmapF (_compose f' g') y == _compose (fmapF f') (fmapF g') y })
                    -> f:(q -> r)
                    -> g:(p -> q)
                    -> x:Rec1 f p
                    -> { fmapRec1 fmapF (_compose f g) x == _compose (fmapRec1 fmapF f) (fmapRec1 fmapF g) x }
@-}
-}
fmapRec1Compose :: (forall a b. (a -> b) -> f a -> f b)
                -> (forall a b c. (b -> c) -> (a -> b) -> f a -> Proof)
                -> (q -> r) -> (p -> q) -> Rec1 f p -> Proof
fmapRec1Compose fmapF fmapFCompose f g r@(Rec1 fp)
  =   fmapRec1 fmapF (_compose f g) r
  ==. fmapRec1 fmapF (_compose f g) (Rec1 fp)
  ==. Rec1 (fmapF (_compose f g) fp)
  ==. Rec1 (_compose (fmapF f) (fmapF g) fp) ? fmapFCompose f g fp
  ==. Rec1 (fmapF f (fmapF g fp))
  ==. fmapRec1 fmapF f (Rec1 (fmapF g fp))
  ==. fmapRec1 fmapF f (fmapRec1 fmapF g (Rec1 fp))
  ==. _compose (fmapRec1 fmapF f) (fmapRec1 fmapF g) (Rec1 fp)
  ==. _compose (fmapRec1 fmapF f) (fmapRec1 fmapF g) r
  *** QED
-}

{-
vfunctorRec1 :: VerifiedFunctor f -> VerifiedFunctor (Rec1 f)
vfunctorRec1 (VerifiedFunctor fmapF fmapFId fmapFCompose)
  = VerifiedFunctor (fmapRec1        fmapF)
                    (fmapRec1Id      fmapF fmapFId)
                    (fmapRec1Compose fmapF fmapFCompose)
-}
