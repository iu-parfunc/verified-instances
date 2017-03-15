module Control.Delay where

open import Agda.Builtin.Size

-- Bove-Capretta delay monad

mutual
  data Delay (A : Set) (i : Size) : Set where
    now   : A → Delay A i
    later : ∞Delay A i → Delay A i

  record ∞Delay (A : Set) (i : Size) : Set where
    coinductive
    field
      coe : {j : Size< i} → Delay A j
