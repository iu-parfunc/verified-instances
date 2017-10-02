{-@ LIQUID "--higherorder" @-}
{-# LANGUAGE Rank2Types #-}

module Data.Iso where

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
                         , tof1  :: forall a. y:(g a) -> { to1 (from1 y) == y }
                         , fot1  :: forall a. x:(f a) -> { from1 (to1 x) == x }
                         }
@-}
data Iso1 f g = Iso1 { to1   :: forall a. f a -> g a
                     , from1 :: forall a. g a -> f a
                     , tof1  :: forall a. g a -> Proof
                     , fot1  :: forall a. f a -> Proof
                     }
