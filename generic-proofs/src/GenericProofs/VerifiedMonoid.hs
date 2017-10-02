{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exactdc"        @-}
module GenericProofs.VerifiedMonoid where

import GenericProofs.Iso
import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (Monoid(..))

{-@ data VerifiedMonoid a = VerifiedMonoid {
      mappend :: a -> a -> a
    , mappendAssoc :: x:a -> y:a -> z:a
                   -> { mappend x (mappend y z) == mappend (mappend x y) z }
    , mempty  :: a
    , lMempty :: x:a -> { mappend mempty x == x }
    , rMempty :: x:a -> { mappend x mempty == x }
    }
@-}
data VerifiedMonoid a = VerifiedMonoid {
    mappend      :: a -> a -> a
  , mappendAssoc :: a -> a -> a -> Proof
  , mempty       :: a
  , lMempty      :: a -> Proof
  , rMempty      :: a -> Proof
  }
infixr 6 `mappend`

{-@ axiomatize mappendInv @-}
mappendInv :: (a -> a -> a)
           -> (a -> b) -> (b -> a)
           -> b -> b -> b
mappendInv mappendA f g x y = f (mappendA (g x) (g y))
{-# INLINE mappendInv #-}

{-@ mappendInvAssoc :: mappendA:(a -> a -> a)
                    -> mappendAAssoc:(i:a -> j:a -> k:a -> { mappendA i (mappendA j k) == mappendA (mappendA i j) k })
                    -> f:(a -> b)
                    -> g:(b -> a)
                    -> gof:(z:a -> { g (f z) == z })
                    -> x:b
                    -> y:b
                    -> z:b
                    -> { mappendInv mappendA f g x (mappendInv mappendA f g y z) == mappendInv mappendA f g (mappendInv mappendA f g x y) z }
@-}
mappendInvAssoc :: (a -> a -> a)
                -> (a -> a -> a -> Proof)
                -> (a -> b)
                -> (b -> a)
                -> (a -> Proof)
                -> b -> b -> b
                -> Proof
mappendInvAssoc mappendA mappendAAssoc f g gof x y z
  =   mappendInv mappendA f g x (mappendInv mappendA f g y z)
  ==. mappendInv mappendA f g x (f (mappendA (g y) (g z)))
  ==. f (mappendA (g x) (g (f (mappendA (g y) (g z)))))
  ==. f (mappendA (g x) (mappendA (g y) (g z))) ? gof (mappendA (g y) (g z))
  ==. f (mappendA (mappendA (g x) (g y)) (g z)) ? mappendAAssoc (g x) (g y) (g z)
  ==. f (mappendA (g (f (mappendA (g x) (g y)))) (g z)) ? gof (mappendA (g x) (g y))
  ==. f (mappendA (g (mappendInv mappendA f g x y)) (g z))
  ==. mappendInv mappendA f g (mappendInv mappendA f g x y) z
  *** QED

{-@ axiomatize memptyInv @-}
memptyInv :: a -> (a -> b) -> b
memptyInv x f = f x

{-@ lMemptyInv :: f:(a -> b)
               -> g:(b -> a)
               -> fog:(z:b -> { f (g z) == z })
               -> gof:(z:a -> { g (f z) == z })
               -> memptyA:a
               -> mappendA:(a -> a -> a)
               -> lMemptyA:(z:a -> { mappendA memptyA z == z })
               -> x:b
               -> { mappendInv mappendA f g (memptyInv memptyA f) x == x }
@-}
lMemptyInv :: (a -> b)
           -> (b -> a)
           -> (b -> Proof)
           -> (a -> Proof)
           -> a
           -> (a -> a -> a)
           -> (a -> Proof)
           -> b
           -> Proof
lMemptyInv f g fog gof memptyA mappendA lMemptyA x
  =   mappendInv mappendA f g (memptyInv memptyA f) x
  ==. mappendInv mappendA f g (f memptyA) x
  ==. f (mappendA (g (f memptyA)) (g x))
  ==. f (mappendA memptyA (g x)) ? gof memptyA
  ==. f (g x) ? lMemptyA (g x)
  ==. x ? fog x
  *** QED

{-@ rMemptyInv :: f:(a -> b)
               -> g:(b -> a)
               -> fog:(z:b -> { f (g z) == z })
               -> gof:(z:a -> { g (f z) == z })
               -> memptyA:a
               -> mappendA:(a -> a -> a)
               -> rMemptyA:(z:a -> { mappendA z memptyA == z })
               -> x:b
               -> { mappendInv mappendA f g x (memptyInv memptyA f) == x }
@-}
rMemptyInv :: (a -> b)
           -> (b -> a)
           -> (b -> Proof)
           -> (a -> Proof)
           -> a
           -> (a -> a -> a)
           -> (a -> Proof)
           -> b
           -> Proof
rMemptyInv f g fog gof memptyA mappendA rMemptyA x
  =   mappendInv mappendA f g x (memptyInv memptyA f)
  ==. mappendInv mappendA f g x (f memptyA)
  ==. f (mappendA (g x) (g (f memptyA)))
  ==. f (mappendA (g x) memptyA) ? gof memptyA
  ==. f (g x) ? rMemptyA (g x)
  ==. x ? fog x
  *** QED

{-@ vmonoidInv :: f:(a -> b)
               -> g:(b -> a)
               -> fog:(x:b -> { f (g x) == x })
               -> gof:(x:a -> { g (f x) == x })
               -> VerifiedMonoid a
               -> VerifiedMonoid b
@-}
vmonoidInv :: (a -> b) -> (b -> a) -> (b -> Proof) -> (a -> Proof)
           -> VerifiedMonoid a -> VerifiedMonoid b
vmonoidInv f g fog gof
           (VerifiedMonoid mappendA mappendAssocA memptyA lMemptyA rMemptyA)
  = VerifiedMonoid (mappendInv      mappendA f g)
                   (mappendInvAssoc mappendA mappendAssocA f g gof)
                   (memptyInv memptyA f)
                   (lMemptyInv f g fog gof memptyA mappendA lMemptyA)
                   (rMemptyInv f g fog gof memptyA mappendA rMemptyA)

vmonoidIso :: Iso a b -> VerifiedMonoid a -> VerifiedMonoid b
vmonoidIso (Iso f g fog gof) = vmonoidInv f g fog gof
