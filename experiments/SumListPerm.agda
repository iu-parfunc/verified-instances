module _ where

open import Prelude hiding (sum)
open import Data.List.Perm

-- examples:
test₀ : IsPerm {Nat} (1 ∷ []) (1 ∷ [])
test₀ = here ∷ []
test₁ : IsPerm {Nat} (1 ∷ 2 ∷ 3 ∷ []) (2 ∷ 3 ∷ 1 ∷ [])
test₁ = there (there here) ∷ (here ∷ (here ∷ []))
test₂ : IsPerm {Nat} (1 ∷ 2 ∷ 3 ∷ []) (3 ∷ 2 ∷ 1 ∷ [])
test₂ = there (there here) ∷ (there here ∷ (here ∷ []))
test₃ : IsPerm {Nat} (1 ∷ 2 ∷ 3 ∷ []) (1 ∷ 3 ∷ 2 ∷ [])
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
open SumIsInvariantOnPermutation ℕ 0 _+N_ +-comm +-assoc
open SumIsInvariantOnPermutation ℕ 1 _*N_ *-comm *-assoc
