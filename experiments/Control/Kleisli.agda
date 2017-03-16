module Control.Kleisli where

open import Prelude
open import Control.Monad.Zero

-- Kleisli as a relative monad

record Kleisli {a b} (M : Set a → Set b) : Set (lsuc a ⊔ b) where
  no-eta-equality
  constructor kleisli
  field
    retK  : ∀ {X} → X → M X
    bindK : ∀ {A B} → M A → (A → M B) → M B

  _◇_ : ∀ {A B C : Set a} → (B → M C) → (A → M B) → (A → M C)
  (f ◇ g) a = bindK (g a) f

open Kleisli public
