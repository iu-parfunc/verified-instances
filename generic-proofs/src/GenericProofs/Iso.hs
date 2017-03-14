{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--totality"    @-}
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
