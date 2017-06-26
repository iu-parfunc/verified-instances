module _ where

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

-- examples:
test₀ : IsPerm (1 ∷ []) (1 ∷ [])
test₀ = here ∷ []
test₁ : IsPerm (1 ∷ 2 ∷ 3 ∷ []) (2 ∷ 3 ∷ 1 ∷ [])
test₁ = there (there here) ∷ (here ∷ (here ∷ []))
test₂ : IsPerm (1 ∷ 2 ∷ 3 ∷ []) (3 ∷ 2 ∷ 1 ∷ [])
test₂ = there (there here) ∷ (there here ∷ (here ∷ []))
test₃ : IsPerm (1 ∷ 2 ∷ 3 ∷ []) (1 ∷ 3 ∷ 2 ∷ [])
test₃ = here ∷ (there here ∷ (here ∷ []))

-- We need a set with an identity element and a binary operation which
-- is commutative and associative (abelian monoid). The proof doesn't
-- need to use the identity laws however.

module SumIsInvariantOnPermutation
       (A : Set) (e : A) (_<>_ : A → A → A)
       (<>-comm : ∀ m n → m <> n ≡ n <> m)
       (<>-assoc : ∀ m n o → (m <> n) <> o ≡ m <> (n <> o)) where

  sum : List A → A
  sum [] = e
  sum (n ∷ ns) = n <> sum ns

  lemma : ∀ {m ns mns}
        → m ∪ ns ≡ mns → m <> sum ns ≡ sum mns
  lemma here = refl
  lemma {m} {n ∷ ns} (there p)
    rewrite sym (<>-assoc m n (sum ns))
          | <>-comm m n
          | <>-assoc n m (sum ns)
          | lemma p = refl

  theorem : ∀ {ms ns}
          → IsPerm ms ns → sum ms ≡ sum ns
  theorem [] = refl
  theorem (here ∷ p) rewrite theorem p = refl
  theorem {m ∷ _} {n ∷ _} (there {ns = ns} p ∷ p')
    rewrite theorem p'
          | sym (<>-assoc m n (sum ns))
          | <>-comm m n
          | <>-assoc n m (sum ns)
          | lemma p = refl

open import Data.Nat
open import Data.Nat.Properties.Simple

-- works with + and *
open SumIsInvariantOnPermutation ℕ 0 _+_ +-comm +-assoc
open SumIsInvariantOnPermutation ℕ 1 _*_ *-comm *-assoc
