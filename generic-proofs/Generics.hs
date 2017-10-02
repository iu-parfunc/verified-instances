-- Generics.hs
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exactdc"        @-}
{-# LANGUAGE RankNTypes #-}
module Generics where

import VF
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize _identity @-}
_identity :: a -> a
_identity x = x
{-# INLINE _identity #-}

{-@ data Par1 p = Par1 { unPar1 :: p } @-}
data Par1 p = Par1 { unPar1 :: p }

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
