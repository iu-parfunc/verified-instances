{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exactdc"         @-}
{-# LANGUAGE RankNTypes #-}
module GenericProofs.VerifiedFunctor where

import Language.Haskell.Liquid.ProofCombinators

-- import GenericProofs.Iso
import GenericProofs.Utils

{-@
data VerifiedFunctor m = VerifiedFunctor {
    fmap        :: forall a b. (a -> b) -> m a -> m b
  , fmapId      :: forall a. x:m a -> { fmap identity x == x }
  , fmapCompose :: forall a b c. f:(b -> c) -> g:(a -> b) -> x:m a
                -> { fmap (compose f g) x == compose (fmap f) (fmap g) x }
  }
@-}
data VerifiedFunctor m = VerifiedFunctor {
    fmap        :: forall a b. (a -> b) -> m a -> m b
  , fmapId      :: forall a. m a -> Proof
  , fmapCompose :: forall a b c. (b -> c) -> (a -> b) -> m a -> Proof
  }

{-
{-@ axiomatize functorInvFmap @-}
functorInvFmap :: (forall a. f a -> g a)
               -> (forall a. g a -> f a)
               -> (forall a b. (a -> b) -> f a -> f b)
               -> (p -> q)
               -> g p
               -> g q
functorInvFmap f t fmapF h x = f (fmapF h (t x))

{-@ functorInvFmapId :: f:(forall a. f a -> g a)
                     -> t:(forall a. g a -> f a)
                     -> fot:(forall a. x:(g a) -> { f (t x) == x })
                     -> fmapF:(forall a b. (a -> b) -> f a -> f b)
                     -> fmapFId:(forall a. x:(f a) -> { fmapF identity x == x })
                     -> y:(g p)
                     -> { functorInvFmap f t fmapF identity y == y }
@-}
functorInvFmapId :: (forall a. f a -> g a)
                 -> (forall a. g a -> f a)
                 -> (forall a. g a -> Proof)
                 -> (forall a b. (a -> b) -> f a -> f b)
                 -> (forall a. f a -> Proof)
                 -> g p
                 -> Proof
functorInvFmapId f t fot fmapF fmapFId y
  =   functorInvFmap f t fmapF identity y
  ==. f (fmapF identity (t y))
  ==. f (t y) ? fmapFId (t y)
  ==. y ? fot y
  *** QED

{-@ functorInvFmapCompose :: fro:(forall a. f a -> g a)
                          -> t:(forall a. g a -> f a)
                          -> tof:(forall a. x:(f a) -> { t (fro x) == x })
                          -> fmapF:(forall a b. (a -> b) -> f a -> f b)
                          -> fmapFCompose:(forall a b c. f':(b -> c) -> g':(a -> b) -> x:(f a) -> { fmapF (compose f' g') x == compose (fmapF f') (fmapF g') x })
                          -> f:(q -> r)
                          -> g:(p -> q)
                          -> y:(g p)
                          -> { functorInvFmap fro t fmapF (compose f g) y == compose (functorInvFmap fro t fmapF f) (functorInvFmap fro t fmapF g) y }
@-}
functorInvFmapCompose :: (forall a. f a -> g a)
                      -> (forall a. g a -> f a)
                      -> (forall a. f a -> Proof)
                      -> (forall a b. (a -> b) -> f a -> f b)
                      -> (forall a b c. (b -> c) -> (a -> b) -> f a -> Proof)
                      -> (q -> r)
                      -> (p -> q)
                      -> g p
                      -> Proof
functorInvFmapCompose fro t tof fmapF fmapFCompose f g y
  =   functorInvFmap fro t fmapF (compose f g) y
  ==. fro (fmapF (compose f g) (t y))
  ==. fro (compose (fmapF f) (fmapF g) (t y)) ? fmapFCompose f g (t y)
  ==. fro (fmapF f (fmapF g (t y)))
  ==. fro (fmapF f (t (fro (fmapF g (t y))))) ? tof (fmapF g (t y))
  ==. functorInvFmap fro t fmapF f (fro (fmapF g (t y)))
  ==. functorInvFmap fro t fmapF f (functorInvFmap fro t fmapF g y)
  ==. compose (functorInvFmap fro t fmapF f) (functorInvFmap fro t fmapF g) y
  *** QED

vfunctorInv :: (forall a. f a -> g a) -> (forall a. g a -> f a)
            -> (forall a. g a -> Proof) -> (forall a. f a -> Proof)
            -> VerifiedFunctor f -> VerifiedFunctor g
vfunctorInv f t fot tof (VerifiedFunctor fmapF fmapFId fmapFCompose)
  = VerifiedFunctor (functorInvFmap        f t fmapF)
                    (functorInvFmapId      f t fot fmapF fmapFId)
                    (functorInvFmapCompose f t tof fmapF fmapFCompose)

vfunctorIso :: Iso1 f g -> VerifiedFunctor f -> VerifiedFunctor g
vfunctorIso (Iso1 t f tof fot) = vfunctorInv t f tof fot
{-# INLINE vfunctorIso #-}
-}
