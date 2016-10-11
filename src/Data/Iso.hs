{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}

module Data.Iso where

import Language.Haskell.Liquid.ProofCombinators

{-@ data Iso a b = Iso { f   :: a -> b
                       , g   :: b -> a
                       , fog :: y:b -> { f (g y) == y }
                       , gof :: x:a -> { g (f x) == x }
                       }
@-}

data Iso a b = Iso { f   :: a -> b
                   , g   :: b -> a
                   , fog :: b -> Proof
                   , gof :: a -> Proof
                   }
