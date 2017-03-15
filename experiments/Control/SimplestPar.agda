{-# OPTIONS --type-in-type #-}

module Control.SimplestPar where

open import Builtin.Size
open import Prelude
open import Builtin.Float
open import Builtin.Coinduction
open import Control.Operational

Val : Set
Val = Float

data IVar (A : Set) : Set where
  ivar : Int → IVar A

data Heap (A : Set) : Set where
  ε   : Heap A
  _,∅ : Heap A → Heap A
  _,_ : Heap A → IVar A → Heap A

data _∈_ {A : Set} (x : IVar A) : Heap A → Set where
  here : x ∈ (ε , x)
  there : ∀ {Γ y} → x ∈ Γ → x ∈ (Γ , y)
  -- somewhere : ∀ {Γ} → x ∈ Γ → x ∈ (Γ ,∅)

data Trace {A : Set} : Heap A → Set → Set where
  Get  : ∀ {Γ} → (x : IVar A) (p : x ∈ Γ) → Trace Γ A
  Put  : ∀ {Γ} → (x : IVar A) → A → Trace (Γ , x) A
  New  : ∀ {Γ} → Trace (Γ ,∅) A
  -- Fork : Trace A → Trace A → Trace A
  Done : ∀ {Γ} → Trace Γ Unit

Par : Set → Set
Par A = Op (Trace {Val} ε) A

data Stream (A : Set) : Set where
  _∷_ : (a : A) (as : ∞ (Stream A)) → Stream A

instance
  FunctorStream : Functor Stream
  fmap {{FunctorStream}} f (a ∷ as) = f a ∷ ♯ fmap f (♭ as)
