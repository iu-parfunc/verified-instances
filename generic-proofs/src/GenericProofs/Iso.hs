{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--totality"    @-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
module GenericProofs.Iso (
    Iso(..)
  , isoRefl
  , isoCompose
  , isoSym
  , isoTrans

  , Iso1(..)
  ) where

import Control.Category                         (Category (..))
import Language.Haskell.Liquid.ProofCombinators

{-@ data Iso a b = Iso { to   :: a -> b
                       , from :: b -> a
                       , tof  :: y:b -> { to (from y) == y }
                       , fot  :: x:a -> { from (to x) == x }
                       }
@-}

data Iso a b = Iso { to   :: a -> b
                   , from :: b -> a
                   , tof  :: b -> Proof
                   , fot  :: a -> Proof
                   }

{-@ data Iso1 f g = Iso1 { to1   :: forall a. f a -> g a
                         , from1 :: forall a. g a -> f a
                         , tof1  :: forall a. g a -> Proof
                         , fot1  :: forall a. f a -> Proof
                         }
@-}
data Iso1 f g = Iso1 { to1   :: forall a. f a -> g a
                     , from1 :: forall a. g a -> f a
                     , tof1  :: forall a. g a -> Proof
                     , fot1  :: forall a. f a -> Proof
                     }

instance Category Iso where
  id  = isoRefl
  (.) = isoCompose

-- Sadly, LH seems to have trouble with id
{-@ axiomatize identity @-}
identity :: a -> a
identity x = x
{-# INLINE identity #-}

-- | The identity Iso.
isoRefl :: Iso a a
isoRefl = Iso identity
              identity
              (\x -> identity (identity x) ==. x *** QED)
              (\x -> identity (identity x) ==. x *** QED)

-- | Isos are symmetric.
isoSym :: Iso a b -> Iso b a
isoSym (Iso { to, from, tof, fot }) = Iso from to fot tof

-- Sadly, LH seems to have trouble with (.)
{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)
{-# INLINE compose #-}

{-@ compInverse :: to1:(b -> c)
                -> from1:(c -> b)
                -> fot1:(y:b -> { from1 (to1 y) == y })
                -> to2:(a -> b)
                -> from2:(b -> a)
                -> fot2:(x:a -> { from2 (to2 x) == x })
                -> x:a -> { compose from2 from1 (compose to1 to2 x) == x }
@-}
compInverse :: (b -> c) -> (c -> b) -> (b -> Proof)
            -> (a -> b) -> (b -> a) -> (a -> Proof)
            -> a -> Proof
compInverse to1 from1 fot1 to2 from2 fot2 x
  =   compose from2 from1 (compose to1 to2 x)
  ==. from2 (from1 (to1 (to2 x)))
  ==. from2 (to2 x) ? fot1 (to2 x)
  ==. x             ? fot2 x
  *** QED

-- | Isos compose.
isoCompose :: Iso b c -> Iso a b -> Iso a c
isoCompose (Iso toBC fromBC tofBC fotBC)
           (Iso toAB fromAB tofAB fotAB)
  = Iso (compose toBC toAB)
        (compose fromAB fromBC)
        (compInverse fromAB toAB tofAB fromBC toBC tofBC)
        (compInverse toBC fromBC fotBC toAB fromAB fotAB)

-- | Isos are transitive.
isoTrans :: Iso a b -> Iso b c -> Iso a c
isoTrans = flip isoCompose
