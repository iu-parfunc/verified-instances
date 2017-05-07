{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exactdc"         @-}
module GenericProofs.Utils (compose, identity) where

{-@ axiomatize identity @-}
identity :: a -> a
identity x = x
{-# INLINE identity #-}

{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)
{-# INLINE compose #-}
