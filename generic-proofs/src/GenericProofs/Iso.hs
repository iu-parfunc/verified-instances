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
  , iso1Refl
  -- , iso1Compose
  , iso1Sym
  -- , iso1Trans
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

{-
instance Category Iso1 where
  id  = iso1Refl
  (.) = iso1Compose
-}

-- Sadly, LH seems to have trouble with id
{-@ axiomatize identity @-}
identity :: a -> a
identity x = x
{-# INLINE identity #-}

-- | The identity 'Iso'.
isoRefl :: Iso a a
isoRefl = Iso identity
              identity
              (\x -> identity (identity x) ==. x *** QED)
              (\x -> identity (identity x) ==. x *** QED)

-- | The identity 'Iso1'.
iso1Refl :: Iso1 f f
iso1Refl = Iso1 identity
                identity
                (\x -> identity (identity x) ==. x *** QED)
                (\x -> identity (identity x) ==. x *** QED)

-- | 'Iso's are symmetric.
isoSym :: Iso a b -> Iso b a
isoSym (Iso { to, from, tof, fot }) = Iso from to fot tof

-- | 'Iso1's are symmetric.
iso1Sym :: Iso1 f g -> Iso1 g f
iso1Sym (Iso1 { to1, from1, tof1, fot1 }) = Iso1 from1 to1 fot1 tof1

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

{-
{-@ comp1Inverse :: to1:(g a -> h a)
                 -> from1:(h a -> g a)
                 -> fot1:(y:(g a) -> { from1 (to1 y) == y })
                 -> to2:(f a -> g a)
                 -> from2:(g a -> f a)
                 -> fot2:(x:(f a) -> { from2 (to2 x) == x })
                 -> x:(f a) -> { compose from2 from1 (compose to1 to2 x) == x }
@-}
comp1Inverse :: (g a -> h a) -> (h a -> g a) -> (g a -> Proof)
             -> (f a -> g a) -> (g a -> f a) -> (f a -> Proof)
             -> f a -> Proof
comp1Inverse to1 from1 fot1 to2 from2 fot2 x
  =   compose from2 from1 (compose to1 to2 x)
  ==. from2 (from1 (to1 (to2 x)))
  ==. from2 (to2 x) ? fot1 (to2 x)
  ==. x             ? fot2 x
  *** QED
-}

-- | 'Iso's compose.
isoCompose :: Iso b c -> Iso a b -> Iso a c
isoCompose (Iso toBC fromBC tofBC fotBC)
           (Iso toAB fromAB tofAB fotAB)
  = Iso (compose toBC toAB)
        (compose fromAB fromBC)
        (compInverse fromAB toAB tofAB fromBC toBC tofBC)
        (compInverse toBC fromBC fotBC toAB fromAB fotAB)

{-
-- | 'Iso1's compose.
iso1Compose :: Iso1 g h -> Iso1 f g -> Iso1 f h
iso1Compose (Iso1 to1GH from1GH tof1GH fot1GH)
            (Iso1 to1FG from1FG tof1FG fot1FG)
  = Iso1 (compose to1GH to1FG)
         (compose from1FG from1GH)
         (comp1Inverse from1FG to1FG tof1FG from1GH to1GH tof1GH)
         (comp1Inverse to1GH from1GH fot1GH to1FG from1FG fot1FG)
-}

-- | 'Iso's are transitive.
isoTrans :: Iso a b -> Iso b c -> Iso a c
isoTrans = flip isoCompose

{-
-- | 'Iso1's are transitive.
iso1Trans :: Iso1 f g -> Iso1 g h -> Iso1 f h
iso1Trans = flip iso1Compose
-}
