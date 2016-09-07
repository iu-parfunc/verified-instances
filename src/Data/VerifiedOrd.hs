{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}

module Data.VerifiedOrd (VerifiedOrd, leqOrd, cmpOrd, (==)) where

import Prelude hiding ((==))
import Language.Haskell.Liquid.ProofCombinators

data VerifiedOrd a = LEq (a -> a -> Bool) | Cmp (a -> a -> Ordering)

{-@
leqOrd :: leq:(a -> a -> Bool)
       -> (x:a -> y:a -> { v:() | Prop (leq x y) || Prop (leq y x) })
       -> (x:a -> y:a -> { v:() | Prop (leq x y) || Prop (leq y x) ==> x == y })
       -> (x:a -> y:a -> z:a -> { v:() | Prop (leq x y) && Prop (leq y z) ==> Prop (leq x z) })
       -> VerifiedOrd a
 @-}
leqOrd :: (a -> a -> Bool)
       -> (a -> a -> Proof)
       -> (a -> a -> Proof)
       -> (a -> a -> a -> Proof)
       -> VerifiedOrd a
leqOrd leq total antisym trans = LEq leq

-- TODO
cmpOrd :: (a -> a -> Ordering) -> VerifiedOrd a
cmpOrd cmp = undefined

(==) :: VerifiedOrd a -> a -> a -> Bool
(==) (LEq f) x y = f x y
(==) (Cmp f) x y = case f x y of { GT -> False ; _ -> True }
