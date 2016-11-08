{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--totality"           @-}
{-@ LIQUID "--exactdc"            @-}

module Data.VerifiedMonoid.Instances.Prod (vmonoidProd) where

import Data.VerifiedMonoid
import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize identProd @-}
identProd :: a -> b -> (a, b)
identProd x y = (x, y)
{-# INLINE identProd #-}

{-@ axiomatize prodProd @-}
prodProd :: (a -> a -> a) -> (b -> b -> b)
         -> (a, b) -> (a, b) -> (a, b)
prodProd proda prodb (x1, y1) (x2, y2) = (proda x1 x2, prodb y1 y2)
{-# INLINE prodProd #-}

{-@ lidentProd :: identa:a -> proda:(a -> a -> a)
               -> lidenta:(x:a -> { proda identa x == x })
               -> identb:b -> prodb:(b -> b -> b)
               -> lidentb:(y:b -> { prodb identb y == y })
               -> p:(a, b)
               -> { prodProd proda prodb (identProd identa identb) p == p }
@-}
lidentProd :: a -> (a -> a -> a) -> (a -> Proof)
           -> b -> (b -> b -> b) -> (b -> Proof)
           -> (a, b) -> Proof
lidentProd identa proda lidenta identb prodb lidentb p@(x, y) =
      prodProd proda prodb (identProd identa identb) p
  ==. prodProd proda prodb (identa, identb) (x, y)
  ==. (proda identa x, prodb identb y)
  ==. (x, prodb identb y) ? lidenta x
  ==. (x, y)              ? lidentb y
  ==. p
  *** QED

{-@ ridentProd :: identa:a -> proda:(a -> a -> a)
               -> ridenta:(x:a -> { proda x identa == x })
               -> identb:b -> prodb:(b -> b -> b)
               -> ridentb:(y:b -> { prodb y identb == y })
               -> p:(a, b)
               -> { prodProd proda prodb p (identProd identa identb) == p }
@-}
ridentProd :: a -> (a -> a -> a) -> (a -> Proof)
           -> b -> (b -> b -> b) -> (b -> Proof)
           -> (a, b) -> Proof
ridentProd identa proda ridenta identb prodb ridentb p@(x, y) =
      prodProd proda prodb p (identProd identa identb)
  ==. prodProd proda prodb (x, y) (identa, identb)
  ==. (proda x identa, prodb y identb)
  ==. (x, prodb y identb) ? ridenta x
  ==. (x, y)              ? ridentb y
  ==. p
  *** QED

{-@ assocProd :: proda:(a -> a -> a)
              -> assoca:(x:a -> y:a -> z:a -> { proda x (proda y z) == proda (proda x y) z })
              -> prodb:(b -> b -> b)
              -> assocb:(x:b -> y:b -> z:b -> { prodb x (prodb y z) == prodb (prodb x y) z })
              -> p:(a, b) -> q:(a, b) -> r:(a, b)
              -> { prodProd proda prodb p (prodProd proda prodb q r)
                == prodProd proda prodb (prodProd proda prodb p q) r }
@-}
assocProd :: (a -> a -> a) -> (a -> a -> a -> Proof)
          -> (b -> b -> b) -> (b -> b -> b -> Proof)
          -> (a, b) -> (a, b) -> (a, b) -> Proof
assocProd proda assoca prodb assocb p@(x1, y1) q@(x2, y2) r@(x3, y3) =
      prodProd proda prodb p (prodProd proda prodb q r)
  ==. prodProd proda prodb (x1, y1) (prodProd proda prodb (x2, y2) (x3, y3))
  ==. prodProd proda prodb (x1, y1) (proda x2 x3, prodb y2 y3)
  ==. (proda x1 (proda x2 x3), prodb y1 (prodb y2 y3))
  ==. (proda (proda x1 x2) x3, prodb y1 (prodb y2 y3)) ? assoca x1 x2 x3
  ==. (proda (proda x1 x2) x3, prodb (prodb y1 y2) y3) ? assocb y1 y2 y3
  ==. prodProd proda prodb (prodProd proda prodb (x1, y1) (x2, y2)) (x3, y3)
  ==. prodProd proda prodb (proda x1 x2, prodb y1 y2) (x3, y3)
  ==. prodProd proda prodb (prodProd proda prodb p q) r
  *** QED

vmonoidProd :: VerifiedMonoid a -> VerifiedMonoid b -> VerifiedMonoid (a, b)
vmonoidProd (VerifiedMonoid identa proda lidenta ridenta assoca) (VerifiedMonoid identb prodb lidentb ridentb assocb) =
  VerifiedMonoid
    (identProd identa identb)
    (prodProd proda prodb)
    (lidentProd identa proda lidenta identb prodb lidentb)
    (ridentProd identa proda ridenta identb prodb ridentb)
    (assocProd proda assoca prodb assocb)
