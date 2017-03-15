{-# OPTIONS --type-in-type --allow-unsolved-metas #-}

module Control.Operational where

open import Agda.Builtin.Size
open import Prelude
open import Control.Monad.Identity

mutual
  data Delay (A : Set) (i : Size) : Set where
    now   : A → Delay A i
    later : ∞Delay A i → Delay A i

  record ∞Delay (A : Set) (i : Size) : Set where
    coinductive
    field
      coe : {j : Size< i} → Delay A j

data OpT (E : Set → Set) (M : Set → Set) (A : Set) : Set where
  lift : (ma : M A) → OpT E M A
  bind : {B : Set} (mb : OpT E M B) → (k : B → OpT E M A) → OpT E M A
  expr  : (e : E A) → OpT E M A

Op : (F : Set → Set) (A : Set) → Set
Op F A = OpT F Identity A

module _ {E : Set → Set} {M : Set → Set} {{_ : Monad M}} where
  instance
    FunctorOpT : Functor (OpT E M)
    fmap {{FunctorOpT}} f (lift ma) = lift (f <$> ma)
    fmap {{FunctorOpT}} f (bind mb k) = bind mb λ b → fmap f (k b)
    fmap {{FunctorOpT}} f (expr e) = bind (expr e) (λ a → lift (pure (f a)))

    ApplicativeOpT : Applicative (OpT E M)
    pure {{ApplicativeOpT}} a = lift (pure a)
    _<*>_ {{ApplicativeOpT}} = monadAp bind

    MonadOpT : Monad (OpT E M)
    _>>=_ {{MonadOpT}} = bind

  module _ {{_ : Functor E}} where

    mutual
      runOpT : {A : Set} {i : Size} → OpT E M A → Delay (M A) i
      runOpT (lift ma) =
        now ma
      runOpT (bind (lift ma) k) =
        -- let p = ma >>= λ b → {!!}
        -- in  later (∞runOpT {!!})
        later (∞runOpT (bind (lift ma) k))
      runOpT (bind (bind ma k) k') =
        later (∞runOpT (bind ma (λ b → bind (k b) k')))
      runOpT (bind (expr e) k) = {!!}
      runOpT (expr e) = now {!!}

      ∞runOpT : {A : Set} {i : Size} → OpT E M A → ∞Delay (M A) i
      ∞Delay.coe (∞runOpT ma) = runOpT ma
