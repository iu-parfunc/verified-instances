{-@ LIQUID "--higherorder"      @-}
{-@ LIQUID "--totality"         @-}
{-@ LIQUID "--exactdc"          @-}
{-# LANGUAGE Rank2Types #-}

module GenericProofs.VerifiedFunctor where

import Language.Haskell.Liquid.ProofCombinators
import Prelude                                  hiding (fmap)

import GenericProofs.Iso

{-@ axiomatize _identity @-}
_identity :: a -> a
_identity x = x
{-# INLINE _identity #-}

{-@ axiomatize _compose @-}
_compose :: (b -> c) -> (a -> b) -> a -> c
_compose f g x = f (g x)
{-# INLINE _compose #-}

{-@
data VerifiedFunctor m = VerifiedFunctor {
    fmap        :: forall a b. (a -> b) -> m a -> m b
  , fmapId      :: forall a. x:m a -> { fmap _identity x == x }
  , fmapCompose :: forall a b c. f:(b -> c) -> g:(a -> b) -> x:m a
                -> { fmap (_compose f g) x == _compose (fmap f) (fmap g) x }
  }
@-}
data VerifiedFunctor m = VerifiedFunctor {
    fmap        :: forall a b. (a -> b) -> m a -> m b
  , fmapId      :: forall a. m a -> Proof
  , fmapCompose :: forall a b c. (b -> c) -> (a -> b) -> m a -> Proof
  }

{-@ axiomatize functorIsoFmap @-}
functorIsoFmap :: (forall a. f a -> g a)
               -> (forall a. g a -> f a)
               -> (forall a b. (a -> b) -> f a -> f b)
               -> (forall a b. (a -> b) -> g a -> g b)
functorIsoFmap to from fmapF f x = to (fmapF f (from x))

{-@ functorIsoFmapId :: to:(forall a. f a -> g a)
                     -> from:(forall a. g a -> f a)
                     -> tof:(forall a. y:(g a) -> { to (from y) == y })
                     -> fmapF:(forall a b. (a -> b) -> f a -> f b)
                     -> fmapFId:(forall a. x:(f a) -> { fmapF _identity x == x })
                     -> forall a. (y:(g a) -> { functorIsoFmap to from fmapF _identity y == y })
@-}
functorIsoFmapId :: (forall a. f a -> g a)
                 -> (forall a. g a -> f a)
                 -> (forall a. g a -> Proof)
                 -> (forall a b. (a -> b) -> f a -> f b)
                 -> (forall a. f a -> Proof)
                 -> (g a -> Proof)
functorIsoFmapId to from tof fmapF fmapFId y
  =   functorIsoFmap to from fmapF _identity y
  ==. to (fmapF _identity (from y))
  ==. to (from y) ? fmapFId (from y)
  ==. y ? tof y
  *** QED

{-@ functorIsoFmapCompose :: to:(forall a. f a -> g a)
                          -> from:(forall a. g a -> f a)
                          -> fot:(forall a. x:(f a) -> { from (to x) == x })
                          -> fmapF:(forall a b. (a -> b) -> f a -> f b)
                          -> fmapFCompose:(forall a b c. f':(b -> c) -> g':(a -> b) -> x:(f a)
                                                      -> { fmapF (_compose f' g') x == _compose (fmapF f') (fmapF g') x })
                          -> forall a b c. (f:(b -> c) -> g:(a -> b) -> y:(g a)
                          -> { functorIsoFmap to from fmapF (_compose f g) y == _compose (functorIsoFmap to from fmapF f) (functorIsoFmap to from fmapF g) y })
@-}
functorIsoFmapCompose :: (forall a. f a -> g a)
                      -> (forall a. g a -> f a)
                      -> (forall a. f a -> Proof)
                      -> (forall a b. (a -> b) -> f a -> f b)
                      -> (forall a b c. (b -> c) -> (a -> b) -> f a -> Proof)
                      -> (b -> c) -> (a -> b) -> g a -> Proof
functorIsoFmapCompose to from fot fmapF fmapFCompose f g y
  =  functorIsoFmap to from fmapF (_compose f g) y
  ==. to (fmapF (_compose f g) (from y))
  ==. to (_compose (fmapF f) (fmapF g) (from y)) ? fmapFCompose f g (from y)
  ==. to (fmapF f (fmapF g (from y)))
  ==. to (fmapF f (from (to (fmapF g (from y))))) ? fot (fmapF g (from y))
  ==. functorIsoFmap to from fmapF f (to (fmapF g (from y)))
  ==. functorIsoFmap to from fmapF f (functorIsoFmap to from fmapF g y)
  ==. _compose (functorIsoFmap to from fmapF f) (functorIsoFmap to from fmapF g) y
  *** QED

vfunctorIso :: Iso1 f g -> VerifiedFunctor f -> VerifiedFunctor g
vfunctorIso (Iso1 to from tof fot) (VerifiedFunctor fmapF fmapFId fmapFCompose) =
    VerifiedFunctor
        (functorIsoFmap to from fmapF)
        (functorIsoFmapId to from tof fmapF fmapFId)
        (functorIsoFmapCompose to from fot fmapF fmapFCompose)
{-# INLINE vfunctorIso #-}
