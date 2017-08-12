{-# OPTIONS --type-in-type #-}

module Control.Concurrency where

open import Prelude
open import Control.Delay

-- Poor man's concurrency monad

-- Since this is not strictly positive, we'll disable the positivity
-- checker for now. This can actually be encoded as the free monad
-- over the signature of Action, see Turing-completeness Totally Free.

{-# NO_POSITIVITY_CHECK #-}
data Action (M : Set → Set) : Set where
  Atom : (a : M (Action M)) → Action M
  Fork : (a₁ a₂ : Action M) → Action M
  Stop : Action M

record Conc (M : Set → Set) (A : Set) : Set where
  constructor conc
  field
    apply : (A → Action M) → Action M
open Conc

module _ {M : Set → Set} where
  instance
    FunctorConc : Functor (Conc M)
    fmap {{FunctorConc}} f ma = conc λ k → apply ma (k ∘ f)

    ApplicativeConc : Applicative (Conc M)
    pure {{ApplicativeConc}} a = conc λ k → k a
    _<*>_ {{ApplicativeConc}} (conc apply₁) (conc apply₂) =
      conc λ bk → apply₁ λ a → apply₂ (λ ab → bk (a ab))

    MonadConc : Monad (Conc M)
    _>>=_ {{MonadConc}} (conc apply') k =
      conc λ k' → apply' λ a → apply (k a) k'

  module _ {{_ : Monad M}} where

    atom : {A : Set} → M A → Conc M A
    atom m =
      conc λ k → Atom $ do a ← m
                        -| return (k a)
    stop : {A : Set} → Conc M A
    stop = conc λ k → Stop

    action : {A : Set} → Conc M A → Action M
    action m = apply m (λ k → Stop)

    par : {A : Set} → Conc M A → Conc M A → Conc M A
    par m₁ m₂ = conc λ k → Fork (apply m₁ k) (apply m₂ k)

    fork : Conc M ⊤ → Conc M ⊤
    fork m = conc λ k → Fork (action m) (k tt)

    {-# TERMINATING #-}
    size : Action M → M Nat
    size (Atom a) = a >>= size
    size (Fork a₁ a₂) = _+_ <$> size a₁ <*> size a₂
    size Stop = return 0

    -- If there was some form of reduction happening here, we could
    -- use sized types to get termination, otherwise we need to use
    -- Delay.
    {-# TERMINATING #-}
    sched : List (Action M) → M ⊤
    sched [] = return tt
    sched (a ∷ as) = case a of
      λ { (Atom am) → do a' ← am
                      -| sched (as ++ [ a' ])
        ; (Fork a₁ a₂) → sched (as ++ a₁ ∷ a₂ ∷ [])
        ; Stop → sched as
        }

    run : {A : Set} → Conc M A → M ⊤
    run m = sched [ action m ]
