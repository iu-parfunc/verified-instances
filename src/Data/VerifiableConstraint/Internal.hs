{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Data.VerifiableConstraint.Internal where

import Data.Proxy
import Data.Reflection
import Data.Constraint
import Control.Newtype
import Data.Constraint.Unsafe

newtype Lift (p :: * -> Constraint) (a :: *) (s :: *) = Lift { lower :: a }

instance Newtype (Lift p a s) a where
  pack = Lift
  unpack = lower

class VerifiableConstraint p where
  data Verified (p :: * -> Constraint) (a :: *) :: *
  reifiedIns :: Reifies s (Verified p a) :- p (Lift p a s)

with :: Verified p a -> (forall s. Reifies s (Verified p a) => Lift p a s) -> a
with d v = reify d (lower . asProxyOf v)
  where
    asProxyOf :: f s -> Proxy s -> f s
    asProxyOf x _ = x

using :: forall p a b. VerifiableConstraint p => Verified p a -> (p a => b) -> b
using d m = reify d $ \(_ :: Proxy s) ->
  let replaceProof :: Reifies s (Verified p a) :- p a
      replaceProof = trans proof reifiedIns
        where proof = unsafeCoerceConstraint :: p (Lift p a s) :- p a
  in m \\ replaceProof
