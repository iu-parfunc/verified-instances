{-@ LIQUID "--higherorder"  @-}
{-@ LIQUID "--totality"     @-}
{-@ LIQUID "--exactdc"      @-}
{-# LANGUAGE EmptyCase     #-}
{-# LANGUAGE Rank2Types    #-}
{-# LANGUAGE TypeOperators #-}

module GenericProofs.VerifiedFunctor.Generics where

import Prelude hiding (fmap)

import GenericProofs.Iso
import GenericProofs.VerifiedFunctor
import Generics.Deriving.Newtypeless.Base.Internal
import Language.Haskell.Liquid.ProofCombinators

{-@ measure fmapV1 @-}
fmapV1 :: (p -> q) -> V1 p -> V1 q
fmapV1 f x = case x of {}

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

{-@ axiomatize fmapU1 @-}
fmapU1 :: (p -> q) -> U1 p -> U1 q
fmapU1 f U1 = U1

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
fmapU1Compose f g U1
  =   fmapU1 (compose f g) U1
  ==. U1
  ==. fmapU1 f (fmapU1 g U1)
  ==. compose (fmapU1 f) (fmapU1 g) U1
  *** QED

vfunctorU1 :: VerifiedFunctor U1
vfunctorU1 = VerifiedFunctor fmapU1 fmapU1Id fmapU1Compose

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

{-@ axiomatize fmapRec1 @-}
fmapRec1 :: (forall a b. (a -> b) -> f a -> f b)
         -> (p -> q) -> Rec1 f p -> Rec1 f q
fmapRec1 fmapF f (Rec1 fp) = Rec1 (fmapF f fp)

{-@ fmapRec1Id :: fmapF:(forall a b. (a -> b) -> f a -> f b)
               -> fmapFId:(forall a. y:(f a) -> { fmapF identity y == y })
               -> r:Rec1 f p
               -> { fmapRec1 fmapF identity r == r }
@-}
fmapRec1Id :: (forall a b. (a -> b) -> f a -> f b)
           -> (forall a. f a -> Proof)
           -> Rec1 f p -> Proof
fmapRec1Id fmapF fmapFId r@(Rec1 fp)
  =   fmapRec1 fmapF identity r
  ==. Rec1 (fmapF identity fp)
  ==. Rec1 (identity fp) ? fmapFId fp
  ==. Rec1 fp
  ==. r
  *** QED

{-@ fmapRec1Compose :: fmapF:(forall a b. (a -> b) -> f a -> f b)
                    -> fmapFCompose:(forall a b c. f':(b -> c) -> g':(a -> b) -> y:(f a)
                                           -> { fmapF (compose f' g') y == compose (fmapF f') (fmapF g') y })
                    -> f:(q -> r)
                    -> g:(p -> q)
                    -> x:Rec1 f p
                    -> { fmapRec1 fmapF (compose f g) x == compose (fmapRec1 fmapF f) (fmapRec1 fmapF g) x }
@-}
fmapRec1Compose :: (forall a b. (a -> b) -> f a -> f b)
                -> (forall a b c. (b -> c) -> (a -> b) -> f a -> Proof)
                -> (q -> r) -> (p -> q) -> Rec1 f p -> Proof
fmapRec1Compose fmapF fmapFCompose f g r@(Rec1 fp)
  =   fmapRec1 fmapF (compose f g) r
  ==. fmapRec1 fmapF (compose f g) (Rec1 fp)
  ==. Rec1 (fmapF (compose f g) fp)
  ==. Rec1 (compose (fmapF f) (fmapF g) fp) ? fmapFCompose f g fp
  ==. Rec1 (fmapF f (fmapF g fp))
  ==. fmapRec1 fmapF f (Rec1 (fmapF g fp))
  ==. fmapRec1 fmapF f (fmapRec1 fmapF g (Rec1 fp))
  ==. compose (fmapRec1 fmapF f) (fmapRec1 fmapF g) (Rec1 fp)
  ==. compose (fmapRec1 fmapF f) (fmapRec1 fmapF g) r
  *** QED

vfunctorRec1 :: VerifiedFunctor f -> VerifiedFunctor (Rec1 f)
vfunctorRec1 (VerifiedFunctor fmapF fmapFId fmapFCompose)
  = VerifiedFunctor (fmapRec1        fmapF)
                    (fmapRec1Id      fmapF fmapFId)
                    (fmapRec1Compose fmapF fmapFCompose)

{-@ axiomatize fmapSum @-}
fmapSum :: (forall a b. (a -> b) -> f a -> f b)
        -> (forall a b. (a -> b) -> g a -> g b)
        -> (a -> b) -> Sum f g a -> Sum f g b
fmapSum fmapF fmapG f (L1 x) = L1 (fmapF f x)
fmapSum fmapF fmapG f (R1 y) = R1 (fmapG f y)

{-@ fmapSumId :: fmapF:(forall a b. (a -> b) -> f a -> f b)
              -> fmapFId:(forall a. x:(f a) -> { fmapF identity x == x })
              -> fmapG:(forall a b. (a -> b) -> g a -> g b)
              -> fmapGId:(forall a. y:(g a) -> { fmapG identity y == y })
              -> x:(Sum f g p)
              -> { fmapSum fmapF fmapG identity x == x }
@-}
fmapSumId :: (forall a b. (a -> b) -> f a -> f b)
          -> (forall a. f a -> Proof)
          -> (forall a b. (a -> b) -> g a -> g b)
          -> (forall a. g a -> Proof)
          -> Sum f g p -> Proof
fmapSumId fmapF fmapFId fmapG fmapGId (L1 x)
  =   L1 (fmapF identity x)
  ==. L1 x ? fmapFId x
  *** QED
fmapSumId fmapF fmapFId fmapG fmapGId (R1 y)
  =   R1 (fmapG identity y)
  ==. R1 y ? fmapGId y
  *** QED

{-@ fmapSumCompose :: fmapF:(forall a b. (a -> b) -> f a -> f b)
                   -> fmapFCompose:(forall a b c. f':(b -> c) -> g':(a -> b) -> x:(f a)
                                               -> { fmapF (compose f' g') x == compose (fmapF f') (fmapF g') x })
                   -> fmapG:(forall a b. (a -> b) -> g a -> g b)
                   -> fmapGCompose:(forall a b c. f':(b -> c) -> g':(a -> b) -> y:(g a)
                                               -> { fmapG (compose f' g') y == compose (fmapG f') (fmapG g') y })
                   -> forall a b c. (f':(b -> c) -> g':(a -> b) -> u:(Sum f g a)
                   -> { fmapSum fmapF fmapG (compose f' g') u == compose (fmapSum fmapF fmapG f') (fmapSum fmapF fmapG g') u })
@-}
fmapSumCompose :: (forall a b. (a -> b) -> f a -> f b)
               -> (forall a b c. (b -> c) -> (a -> b) -> f a -> Proof)
               -> (forall a b. (a -> b) -> g a -> g b)
               -> (forall a b c. (b -> c) -> (a -> b) -> g a -> Proof)
               -> (forall a b c. (b -> c) -> (a -> b) -> Sum f g a -> Proof)
fmapSumCompose fmapF fmapFCompose fmapG fmapGCompose f' g' u@(L1 x)
  =   fmapSum fmapF fmapG (compose f' g') u
  ==. L1 (fmapF (compose f' g') x)
  ==. L1 (compose (fmapF f') (fmapF g') x) ? fmapFCompose f' g' x
  ==. compose (fmapSum fmapF fmapG f') (fmapSum fmapF fmapG g') u
  *** QED
fmapSumCompose fmapF fmapFCompose fmapG fmapGCompose f' g' u@(R1 y)
  =   fmapSum fmapF fmapG (compose f' g') u
  ==. R1 (fmapG (compose f' g') y)
  ==. R1 (compose (fmapG f') (fmapG g') y) ? fmapGCompose f' g' y
  ==. compose (fmapSum fmapF fmapG f') (fmapSum fmapF fmapG g') u
  *** QED

vfunctorSum :: VerifiedFunctor f -> VerifiedFunctor g -> VerifiedFunctor (Sum f g)
vfunctorSum (VerifiedFunctor fmapF fmapFId fmapFCompose) (VerifiedFunctor fmapG fmapGId fmapGCompose) =
    VerifiedFunctor
        (fmapSum fmapF fmapG)
        (fmapSumId fmapF fmapFId fmapG fmapGId)
        (fmapSumCompose fmapF fmapFCompose fmapG fmapGCompose)

{-@ axiomatize fmapProd @-}
fmapProd :: (forall a b. (a -> b) -> f a -> f b)
         -> (forall a b. (a -> b) -> g a -> g b)
         -> (a -> b) -> Product f g a -> Product f g b
fmapProd fmapF fmapG f (Product x y) = Product (fmapF f x) (fmapG f y)

{-@ fmapProdId :: fmapF:(forall a b. (a -> b) -> f a -> f b)
               -> fmapFId:(forall a. x:(f a) -> { fmapF identity x == x })
               -> fmapG:(forall a b. (a -> b) -> g a -> g b)
               -> fmapGId:(forall a. y:(g a) -> { fmapG identity y == y })
               -> (forall a. x:(Product f g a) -> { fmapProd fmapF fmapG identity x == x })
@-}
fmapProdId :: (forall a b. (a -> b) -> f a -> f b)
           -> (forall a. f a -> Proof)
           -> (forall a b. (a -> b) -> g a -> g b)
           -> (forall a. g a -> Proof)
           -> (forall a. Product f g a -> Proof)
fmapProdId fmapF fmapFId fmapG fmapGId p@(Product x y)
  =   fmapProd fmapF fmapG identity p
  ==. Product (fmapF identity x) (fmapG identity y)
  ==. Product x (fmapG identity y) ? fmapFId x
  ==. Product x y ? fmapGId y
  *** QED

{-@ fmapProdCompose :: fmapF:(forall a b. (a -> b) -> f a -> f b)
                    -> fmapFCompose:(forall a b c. f':(b -> c) -> g':(a -> b) -> x:(f a)
                                                -> { fmapF (compose f' g') x == compose (fmapF f') (fmapF g') x })
                    -> fmapG:(forall a b. (a -> b) -> g a -> g b)
                    -> fmapGCompose:(forall a b c. f':(b -> c) -> g':(a -> b) -> y:(g a)
                                                -> { fmapG (compose f' g') y == compose (fmapG f') (fmapG g') y })
                    -> forall a b c. (f':(b -> c) -> g':(a -> b) -> u:(Product f g a)
                    -> { fmapProd fmapF fmapG (compose f' g') u == compose (fmapProd fmapF fmapG f') (fmapProd fmapF fmapG g') u })
@-}
fmapProdCompose :: (forall a b. (a -> b) -> f a -> f b)
                -> (forall a b c. (b -> c) -> (a -> b) -> f a -> Proof)
                -> (forall a b. (a -> b) -> g a -> g b)
                -> (forall a b c. (b -> c) -> (a -> b) -> g a -> Proof)
                -> (forall a b c. (b -> c) -> (a -> b) -> Product f g a -> Proof)
fmapProdCompose fmapF fmapFCompose fmapG fmapGCompose f' g' u@(Product x y)
  =   fmapProd fmapF fmapG (compose f' g') u
  ==. Product (fmapF (compose f' g') x) (fmapG (compose f' g') y)
  ==. Product (compose (fmapF f') (fmapF g') x) (fmapG (compose f' g') y) ? fmapFCompose f' g' x
  ==. Product (compose (fmapF f') (fmapF g') x) (compose (fmapG f') (fmapG g') y) ? fmapGCompose f' g' y
  ==. compose (fmapProd fmapF fmapG f') (fmapProd fmapF fmapG g') u
  *** QED

vfunctorProduct :: VerifiedFunctor f -> VerifiedFunctor g -> VerifiedFunctor (Product f g)
vfunctorProduct (VerifiedFunctor fmapF fmapFId fmapFCompose) (VerifiedFunctor fmapG fmapGId fmapGCompose) =
    VerifiedFunctor
        (fmapProd fmapF fmapG)
        (fmapProdId fmapF fmapFId fmapG fmapGId)
        (fmapProdCompose fmapF fmapFCompose fmapG fmapGCompose)
