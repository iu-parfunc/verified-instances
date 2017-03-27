{-# OPTIONS --type-in-type #-}

module Control.ConcurrencyFree where

open import Prelude
open import Control.TotallyFree

data Action (E : Set) : Set where
  Atom : (e : E) → Action E
  Fork : (a₁ a₂ : Action E) → Action E
  Stop : Action E

Conc : (A : Set) → Set
Conc A = Π (Action A) (λ a → Action A)
