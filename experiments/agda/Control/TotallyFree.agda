{-# OPTIONS --type-in-type #-}

module Control.TotallyFree where

open import Prelude
open import Builtin.Size
open import Control.Delay
open import Control.Kleisli

-- Turing-Completeness Totally Free

data Free (S : Set) (T : S → Set) (X : Set) : Set where
  ret : (x : X) → Free S T X
  ask : (s : S) → (k : T s → Free S T X) → Free S T X

module _ {S : Set} {T : S → Set} where
  instance
    FunctorFree : Functor (Free S T)
    fmap {{FunctorFree}} f (ret x) = ret (f x)
    fmap {{FunctorFree}} f (ask s k) = ask s (λ t → fmap f (k t))

    ApplicativeFree : Applicative (Free S T)
    pure {{ApplicativeFree}} a = ret a
    _<*>_ {{ApplicativeFree}} (ret f) a = f <$> a
    _<*>_ {{ApplicativeFree}} (ask s k) a = ask s (λ t → k t <*> a)

    MonadFree : Monad (Free S T)
    _>>=_ {{MonadFree}} (ret x) k = k x
    _>>=_ {{MonadFree}} (ask s k) k' = ask s (λ t → k t >>= k')

  call : (s : S) → Free S T (T s)
  call s = ask s ret

Π : (S : Set) (T : S → Set) → Set
Π S T = (s : S) → Free S T (T s)

FreeK : ∀ {S T} → Kleisli (Free S T)
retK FreeK = ret
bindK FreeK = _>>=_

morph : ∀ {S T} {M : Set → Set} (KM : Kleisli M)
      → (h : (s : S) → M (T s))
      → {X : Set} → Free S T X → M X
morph KM h (ret x) = retK KM x
morph KM h (ask s k) = bindK KM (h s) (λ t → morph KM h (k t))

expand : ∀ {S T X} → Π S T → Free S T X → Free S T X
expand f = morph FreeK f

module MaybeExample where

  MaybeK : Kleisli Maybe
  retK MaybeK = just
  bindK MaybeK nothing f = nothing
  bindK MaybeK (just x) f = f x

  already : ∀ {S T X} → Free S T X → Maybe X
  already = morph MaybeK λ s → nothing

  engine : ∀ {S T} (f : Π S T) (n : Nat)
         → {X : Set} → Free S T X → Free S T X
  engine f zero = id
  engine f (suc n) = engine f n ∘ expand f

  fuel : ∀ {S T} → Π S T → Nat → (s : S) → Maybe (T s)
  fuel f n = already ∘ engine f n ∘ f

DelayK : {i : Size} → Kleisli (Delay i)
retK DelayK = return
bindK DelayK = _>>=_

engine : Nat → {X : Set} → Delay _ X → Maybe X
engine _       (now x) = just x
engine zero    (later x') = nothing
engine (suc n) (later x') = engine n (coe x')

mutual
  delay : ∀ {i S T} (f : Π S T) {X : Set} → Free S T X → Delay i X
  delay f = morph DelayK λ s → later (∞delay f (f s))

  ∞delay : ∀ {i S T} (f : Π S T) {X : Set} → Free S T X → ∞Delay i X
  coe (∞delay f g) = delay f g

lazy : ∀ {S T} → Π S T → (s : S) → Delay _ (T s)
lazy f = delay f ∘ f
