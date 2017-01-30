module Control.SimplePar where

open import Prelude hiding (IO)
open import Builtin.Float
open import Builtin.Coinduction

open import Control.Monad.Identity
import Control.Monad.State as S

State : Set → Set → Set
State S = S.StateT S Identity

Val : Set
Val = Float

data IVar (A : Set) : Set where
  ivar : Int → IVar A

data Trace : Set where
  Get  : IVar Val → (Val -> Trace) → Trace
  Put  : IVar Val → Val → Trace → Trace
  New  : (IVar Val -> Trace) → Trace
  Fork : Trace → Trace → Trace
  Done : Trace

record Par (A : Set) : Set where
  constructor par
  field
    runCont : (A → Trace) → Trace

instance
  FunctorPar : Functor Par
  fmap {{FunctorPar}} f (par runCont) = par λ c → runCont (c ∘ f)

  ApplicativePar : Applicative Par
  pure  {{ApplicativePar}} a = par λ c → c a
  _<*>_ {{ApplicativePar}} (par runCont₁) (par runCont₂) =
    par λ bcont → runCont₁ λ a → runCont₂ λ ab → bcont (a ab)

  MonadPar : Monad Par
  _>>=_ {{MonadPar}} (par runCont') k =
    par λ c → runCont' λ a → Par.runCont (k a) c

data Stream (A : Set) : Set where
  _∷_ : (a : A) (as : ∞ (Stream A)) → Stream A

instance
  FunctorStream : Functor Stream
  fmap {{FunctorStream}} f (a ∷ as) = f a ∷ ♯ fmap f (♭ as)

data IntMap (A : Set) : Set where
  ε      : IntMap A
  _↦_,_ : Int → A → IntMap A → IntMap A

find : {A : Set} → Int → IntMap A → Maybe A
find x ε = nothing
find x (y ↦ a , m) =
  ifYes x == y then just a else find x m

remove : {A : Set} → Int → IntMap A → IntMap A
remove x ε = ε
remove x (y ↦ a , m) =
  ifYes x == y
    then remove x m
    else y ↦ a , remove x m

insertWith : {A : Set} → (A → A → A) → Int → A → IntMap A → IntMap A
insertWith f x a ε = x ↦ a , ε
insertWith f x a (y ↦ b , m) =
  ifYes x == y
    then y ↦ f a b , insertWith f x a m
    else x ↦ a     , insertWith f x a m

Heap = IntMap (Maybe Val)
Blkd = IntMap (List (Val → Trace))

data Exn : Set where
  Deadlock : Blkd → Exn
  MultiplePut : Val → Int → Val → Exn

yank : {A : Set} → Nat → A → List A → A × List A
yank n x xs =
  case splitAt (natMod (length (x ∷ xs)) n) (x ∷ xs) of
    λ { (hd , []) → x , hd
      ; (hd , x ∷ tl) → x , hd ++ tl
      }

step : (Trace × List Trace) → Blkd → Int → Heap → Either Exn (List Trace × Blkd × Int × Heap)
sched : Stream Nat → List Trace → Blkd → Int → Heap → Either Exn Heap

{-# TERMINATING #-}
sched randoms [] ε cntr heap =
  return heap
sched randoms [] blkd cntr heap =
  left (Deadlock blkd)
sched (rnd ∷ rs) (t ∷ ts) blkd cntr heap =
  caseM step (yank rnd t ts) blkd cntr heap of
    λ { (threads' , blkd' , cntr' , heap') →
          sched (♭ rs) threads' blkd' cntr' heap' }

step (Get (ivar ix) k , others) blkd cntr heap =
  case join (find ix heap) of
    λ { nothing → return (others , insertWith _++_ ix [ k ] blkd , cntr , heap)
      ; (just v) → return (k v ∷ others , blkd , cntr , heap) }
step (Put (ivar ix) v t₂ , others) blkd cntr heap =
  let heap' = ix ↦ just v , heap
  in case join (find ix heap) of
      λ { nothing → case find ix blkd of
        λ { nothing → return (t₂ ∷ others , blkd , cntr , heap')
          ; (just ls) → return (t₂ ∷ map (λ k → k v) ls ++ others , remove ix blkd , cntr , heap) }
        ; (just v₀) → left (MultiplePut v ix v₀) }
step (New k , others) blkd cntr heap =
  return (k (ivar cntr) ∷ others , blkd , cntr + 1 , cntr ↦ nothing , heap)
step (Fork t₁ t₂ , others) blkd cntr heap =
  return (t₁ ∷ t₂ ∷ others , blkd , cntr , heap)
step (Done , others) blkd cntr heap =
  return (others , blkd , cntr , heap)

data _≤ₕ_ : Heap → Heap → Set where
  ε≤h : ∀ {h} → ε ≤ₕ h
  s≤h : ∀ {x a y b h₁ h₂} → h₁ ≤ₕ h₂ → (x ↦ a , h₁) ≤ₕ (y ↦ b , h₂)

refl≤ₕ : ∀ {h} → h ≤ₕ h
refl≤ₕ {ε} = ε≤h
refl≤ₕ {(x ↦ a , h)} = s≤h refl≤ₕ

mon≤ₕ : ∀ {x a h} → h ≤ₕ (x ↦ a , h)
mon≤ₕ {h = ε} = ε≤h
mon≤ₕ {h = (x ↦ a , h)} = s≤h mon≤ₕ

monotonicity : ∀ {threads} {blkd} {cntr} {heap}
             → ∀ {threads'} {blkd'} {cntr'} {heap'}
             → step threads blkd cntr heap ≡ right (threads' , blkd' , cntr' , heap')
             → heap ≤ₕ heap'
monotonicity {Get (ivar ix) k , others} {heap = heap} p with join (find ix heap)
monotonicity {Get (ivar ix) k , others} refl | nothing = refl≤ₕ
monotonicity {Get (ivar ix) k , others} refl | just v  = refl≤ₕ
monotonicity {Put (ivar ix) v t₂ , others} {heap = heap} p with join (find ix heap)
monotonicity {Put (ivar ix) v t₂ , others} {blkd = blkd} p | nothing with find ix blkd
monotonicity {Put (ivar ix) v t₂ , others} refl | nothing | nothing = mon≤ₕ
monotonicity {Put (ivar ix) v t₂ , others} refl | nothing | just x = refl≤ₕ
monotonicity {Put (ivar ix) v t₂ , others} () | just v₀
monotonicity {New k , others} refl = mon≤ₕ
monotonicity {Fork t₁ t₂ , others} refl = refl≤ₕ
monotonicity {Done , others} refl = refl≤ₕ
