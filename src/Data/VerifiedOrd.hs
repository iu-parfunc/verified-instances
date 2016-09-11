{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}

module Data.VerifiedOrd (
    VerifiedOrd,
    leqOrd,
    cmpOrd,
    (<),
    (<=),
    (>),
    (>=),
    max,
    min,
    ) where

import Prelude hiding ((<), (<=), (>), (>=))
import Language.Haskell.Liquid.ProofCombinators

data VerifiedOrd a = LEq (a -> a -> Bool)
                   | Cmp (a -> a -> Ordering)

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

(<) :: Eq a => VerifiedOrd a -> a -> a -> Bool
(<) (LEq f) x y = f x y && not (x == y)
(<) (Cmp f) x y = case f x y of { LT -> True ; _ -> False }

(<=) :: VerifiedOrd a -> a -> a -> Bool
(<=) (LEq f) x y = f x y
(<=) (Cmp f) x y = case f x y of { GT -> False ; _ -> True }

(>) :: VerifiedOrd a -> a -> a -> Bool
(>) (LEq f) x y = not (f x y)
(>) (Cmp f) x y = case f x y of { GT -> True ; _ -> False }

(>=) :: Eq a => VerifiedOrd a -> a -> a -> Bool
(>=) (LEq f) x y = not (f x y) || x == y
(>=) (Cmp f) x y = case f x y of { LT -> False ; _ -> False }

max :: VerifiedOrd a -> a -> a -> a
max v x y = if ((<=) v x y) then y else x

min :: VerifiedOrd a -> a -> a -> a
min v x y = if ((<=) v x y) then x else y
