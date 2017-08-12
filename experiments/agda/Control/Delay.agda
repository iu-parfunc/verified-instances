module Control.Delay where

open import Builtin.Size
open import Prelude

-- Bove-Capretta delay monad

mutual
  data Delay (i : Size) (A : Set) : Set where
    now   : (a : A) → Delay i A
    later : (a' : ∞Delay i A) → Delay i A

  record ∞Delay (i : Size) (A : Set) : Set where
    coinductive
    constructor ⟨_⟩
    field
      coe : {j : Size< i} → Delay j A

open ∞Delay public

module _ {A B : Set} where
  mutual
    fmapD : ∀ {i} → (A → B) → Delay i A → Delay i B
    fmapD f (now a) = now (f a)
    fmapD f (later a') = later (fmap∞D f a')

    fmap∞D : ∀ {i} → (A → B) → ∞Delay i A → ∞Delay i B
    coe (fmap∞D f a') = fmapD f (coe a')

  mutual
    apD : ∀ {i} → Delay i (A → B) → Delay i A → Delay i B
    apD (now f) a = fmapD f a
    apD (later f') a = later (ap∞D f' a)

    ap∞D : ∀ {i} → ∞Delay i (A → B) → Delay i A → ∞Delay i B
    coe (ap∞D f' a') = apD (coe f') a'

  mutual
    bindD : ∀ {i} → Delay i A → (A → Delay i B) → Delay i B
    bindD (now a) f = f a
    bindD (later a') f = later (bind∞D a' f)

    bind∞D : ∀ {i} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
    coe (bind∞D a' f) = bindD (coe a') f

module _ {i : Size} where
  instance
    FunctorDelay : Functor (Delay i)
    fmap {{FunctorDelay}} = fmapD

    ApplicativeDelay : Applicative (Delay i)
    pure {{ApplicativeDelay}} = now
    _<*>_ {{ApplicativeDelay}} = apD

    MonadDelay : Monad (Delay i)
    _>>=_ {{MonadDelay}} = bindD
