{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--totality"       @-}
{-@ LIQUID "--exactdc"        @-}
module GenericProofs.VerifiedMonoid where

{-
import GenericProofs.Iso
import GenericProofs.VerifiedSemigroup
import Language.Haskell.Liquid.ProofCombinators

{-@ data VerifiedMonoid a = VerifiedMonoid {
      superVS :: VerifiedSemigroup a
    , mempty  :: a
    , lMempty :: x:a -> { sappend superVS mempty x == x }
    , rMempty :: x:a -> { sappend superVS x mempty == x }
    }
@-}
data VerifiedMonoid a = VerifiedMonoid {
    superVS :: VerifiedSemigroup a
  , mempty  :: a
  , lMempty :: a -> Proof
  , rMempty :: a -> Proof
  }

{-@ axiomatize memptyInv @-}
memptyInv :: a -> (a -> b) -> b
memptyInv x f = f x

{-@ lMemptyInv :: f:(a -> b)
               -> g:(b -> a)
               -> fog:(z:b -> { f (g z) == z })
               -> gof:(z:a -> { g (f z) == z })
               -> superVSA:VerifiedSemigroup a
               -> memptyA:a
               -> lMemptyA:(z:a -> { sappend superVSA memptyA z == z })
               -> x:b
               -> { sappend (vsemigroupInv f g gof superVSA) (memptyInv memptyA f) x == x }
@-}
lMemptyInv :: (a -> b)
           -> (b -> a)
           -> (b -> Proof)
           -> (a -> Proof)
           -> VerifiedSemigroup a
           -> a
           -> (a -> Proof)
           -> b
           -> Proof
lMemptyInv f g fog gof superVSA memptyA lMemptyA x
  =   sappend (vsemigroupInv f g gof superVSA) (memptyInv memptyA f) x
  ==. sappendInv (sappend superVSA) f g (memptyInv memptyA f) x
  ==. sappendInv (sappend superVSA) f g (f memptyA) x
  ==. f (sappend superVSA (g (f memptyA)) (g x))
  ==. f (sappend superVSA memptyA (g x)) ? gof memptyA
  ==. f (g x) ? lMemptyA (g x)
  ==. x ? fog x
  *** QED

vmonoidInv :: (a -> b) -> (b -> a) -> (a -> Proof)
           -> VerifiedMonoid a -> VerifiedMonoid b
vmonoidInv f g fog gof (VerifiedMonoid superVSA _memptyA _lMemptyA _rMemptyA)
  = VerifiedMonoid (vsemigroupInv f g gof superVSA)
                   undefined
                   undefined
                   undefined

vmonoidIso :: Iso a b -> VerifiedMonoid a -> VerifiedMonoid b
vmonoidIso (Iso f g fog gof) = vmonoidInv f g fog gof
-}
