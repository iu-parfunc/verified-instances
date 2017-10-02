{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--exactdc"     @-}
{-# LANGUAGE Rank2Types #-}

module Data.Adj where

import Language.Haskell.Liquid.ProofCombinators
import Prelude                                  hiding (id)

{-@ data Id a = I { unI :: a } @-}
data Id a = I { unI :: a }

{-@ data Comp f g a = C { unC :: f (g a) } @-}
data Comp f g a = C { unC :: f (g a) }

{-@ axiomatize id @-}
id :: a -> a
id x = x

------------
-- f -| g --
------------
{-@
data Adj f g = Adj
    { ladj :: forall a b. (f a -> b) -> (a -> g b)
    , radj :: forall a b. (a -> g b) -> (f a -> b)
    , zig  :: forall a. z:g a -> { ladj (radj id) z == z }
    , zag  :: forall a. z:f a -> { radj (ladj id) z == z }
    }
@-}
data Adj f g = Adj
    { ladj :: forall a b. (f a -> b) -> (a -> g b)
    , radj :: forall a b. (a -> g b) -> (f a -> b)
    , zig  :: forall a. g a -> Proof
    , zag  :: forall a. f a -> Proof
    }

{-@ axiomatize eta @-}
eta :: Adj f g -> (forall a. a -> g (f a))
eta (Adj ladj radj zig zag) = ladj id

{-@ axiomatize epsilon @-}
epsilon :: Adj f g -> (forall a. f (g a) -> a)
epsilon (Adj ladj radj zig zag) = radj id

{-@ axiomatize idLadj @-}
idLadj :: (Id a -> b) -> (a -> Id b)
idLadj f x = I (f (I x))

{-@ axiomatize idRadj @-}
idRadj :: (a -> Id b) -> (Id a -> b)
idRadj f (I x) = unI (f x)

{-@ idZig :: z:Id a -> { idLadj (idRadj id) z == z } @-}
idZig :: Id a -> Proof
idZig z@(I x)
  =   idLadj (idRadj id) z
  ==. I (idRadj id (I z))
  ==. I (unI (id z))
  ==. z
  *** QED

{-@ idZag :: z:Id a -> { idRadj (idLadj id) z == z } @-}
idZag :: Id a -> Proof
idZag z@(I x)
  =   idRadj (idLadj id) (I x)
  ==. unI (idLadj id x)
  ==. unI (I (id (I x)))
  ==. z
  *** QED

idAdj :: Adj Id Id
idAdj = Adj idLadj idRadj idZig idZag
