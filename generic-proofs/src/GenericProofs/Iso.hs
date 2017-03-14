{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--totality"    @-}
{-# LANGUAGE NamedFieldPuns #-}
module GenericProofs.Iso where

import GenericProofs.Combinators

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

-- | Isos are symmetric.
isoSym :: Iso a b -> Iso b a
isoSym (Iso { to, from, tof, fot }) = Iso from to fot tof

{-
-- | Isos compose.
isoCompose :: Iso b c -> Iso a b -> Iso a c
isoCompose (Iso toBC fromBC tofBC fotBC)
           (Iso toAB fromAB tofAB fotAB)
  = Iso (toBC . toAB)
        (fromAB . fromBC)
        tofBC
        fotAB
-}
