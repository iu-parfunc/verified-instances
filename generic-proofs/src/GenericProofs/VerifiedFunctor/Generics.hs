{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--totality"       @-}
{-@ LIQUID "--exactdc"        @-}
{-@ LIQUID "--prune-unsorted" @-}
{-# LANGUAGE EmptyCase     #-}
{-# LANGUAGE TypeOperators #-}
module GenericProofs.VerifiedFunctor.Generics where

import GenericProofs.VerifiedFunctor
import Generics.Deriving.Newtypeless
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize identity @-}
identity :: a -> a
identity x = x
{-# INLINE identity #-}

{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)
{-# INLINE compose #-}

{-
{-@ data V1 @-}

{-@ measure fmapV1 :: (p -> q) -> V1 p -> V1 q @-}
fmapV1 :: (p -> q) -> V1 p -> V1 q
fmapV1 _ x = absurd x

absurd :: V1 p -> a
absurd x = case x of {}

{-@ fmapV1Id :: x:V1 p
             -> { fmapV1 identity x == x }
@-}
fmapV1Id :: V1 p -> Proof
fmapV1Id x
 =   fmapV1 identity x
 ==. absurd x
 ==. x
 *** QED

{-@ fmapV1Compose :: f:(q -> r)
                  -> g:(p -> q)
                  -> x:V1 p
                  -> { fmapV1 (compose f g) x == compose (fmapV1 f) (fmapV1 g) x }
@-}
fmapV1Compose :: (q -> r) -> (p -> q)
              -> V1 p -> Proof
fmapV1Compose f g x
  =   fmapV1 (compose f g) x
  ==. absurd x
  ==. fmapV1 f (fmapV1 g x)
  ==. compose (fmapV1 f) (fmapV1 g) x
  *** QED

vfunctorV1 :: VerifiedFunctor V1
vfunctorV1 = VerifiedFunctor fmapV1 fmapV1Id fmapV1Compose
-}

{-@ data U1 p = U1 @-}

{-@ axiomatize fmapU1 @-}
fmapU1 :: (p -> q) -> U1 p -> U1 q
fmapU1 _ _ = U1

{-@ fmapU1Id :: x:U1 p
             -> { fmapU1 identity x == x }
@-}
fmapU1Id :: U1 p -> Proof
fmapU1Id U1
  =   fmapU1 identity U1
  ==. U1
  *** QED

{-@ fmapU1Compose :: f:(q -> r)
                  -> g:(p -> q)
                  -> x:U1 p
                  -> { fmapU1 (compose f g) x == compose (fmapU1 f) (fmapU1 g) x }
@-}
fmapU1Compose :: (q -> r) -> (p -> q)
              -> U1 p -> Proof
fmapU1Compose f g x
  =   fmapU1 (compose f g) x
  ==. U1
  ==. fmapU1 f (fmapU1 g x)
  ==. compose (fmapU1 f) (fmapU1 g) x
  *** QED

vfunctorU1 :: VerifiedFunctor U1
vfunctorU1 = VerifiedFunctor fmapU1 fmapU1Id fmapU1Compose

{-
{-@ data Par1 p = Par1 { unPar1 :: p } @-}

{-@ axiomatize fmapPar1 @-}
fmapPar1 :: (p -> q) -> Par1 p -> Par1 q
fmapPar1 f (Par1 p) = Par1 (f p)

{-@ fmapPar1Id :: x:Par1 p
               -> { fmapPar1 identity x == x }
@-}
fmapPar1Id :: Par1 p -> Proof
fmapPar1Id par@(Par1 p)
  =   fmapPar1 identity par
  ==. Par1 (identity p)
  ==. Par1 p
  ==. par
  *** QED

{-@ fmapPar1Compose :: f:(q -> r)
                    -> g:(p -> q)
                    -> x:Par1 p
                    -> { fmapPar1 (compose f g) x == compose (fmapPar1 f) (fmapPar1 g) x } @-}
fmapPar1Compose :: (q -> r) -> (p -> q)
                -> Par1 p -> Proof
fmapPar1Compose f g x@(Par1 p)
  =   fmapPar1 (compose f g) x
  ==. fmapPar1 (compose f g) (Par1 p)
  ==. Par1 (compose f g p)
  ==. Par1 (f (g p))
  ==. fmapPar1 f (Par1 (g p))
  ==. fmapPar1 f (fmapPar1 g (Par1 p))
  ==. compose (fmapPar1 f) (fmapPar1 g) (Par1 p)
  ==. compose (fmapPar1 f) (fmapPar1 g) x
  *** QED

vfunctorPar1 :: VerifiedFunctor Par1
vfunctorPar1 = VerifiedFunctor fmapPar1 fmapPar1Id fmapPar1Compose
-}
