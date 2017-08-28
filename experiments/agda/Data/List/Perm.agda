module Data.List.Perm where

open import Relation.Binary.PropositionalEquality
open import Data.List hiding (sum)

-- `m ∪ ns ≡ mns` means that inserting `m` somewhere inside `ns` is
-- equal to `mns`. The index tracks the position of `m`.

data _∪_≡_ {A : Set} (m : A) : List A → List A → Set where
  here : ∀ {ms}
       → m ∪ ms ≡ (m ∷ ms)
  there : ∀ {n ns mns}
        → m ∪ ns ≡ mns
        → m ∪ (n ∷ ns) ≡ (n ∷ mns)

-- `IsPerm ms ns` means that `ms` is a permutation of `ns`.

data IsPerm {A : Set} : List A → List A → Set where
  []  : IsPerm [] []
  _∷_ : ∀ {m ms ns mns}
      → m ∪ ns ≡ mns
      → IsPerm ms ns
      → IsPerm (m ∷ ms) mns
