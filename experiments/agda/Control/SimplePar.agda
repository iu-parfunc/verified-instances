module Control.SimplePar where

open import Prelude
open import Builtin.Float
open import Builtin.Coinduction

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

infix 2 _∌_
infix 3 _↦ε,_ _↦_,_

mutual
  data Heap : Set where
    ∅ : Heap
    _↦ε,_ : (ix : Int) → (h : Heap) → ⦃ p : h ∌ ix ⦄ → Heap
    _↦_,_ : (ix : Int) → (v : Val) → (h : Heap) → ⦃ _ : h ∌ ix ⦄ → Heap

  data _∌_ : Heap → Int → Set where
    ∅∌ : {ix : Int} → ∅ ∌ ix
    ε∌ : {ix ix' : Int} {h : Heap}
       → ⦃ _ : h ∌ ix ⦄ ⦃ _ : h ∌ ix' ⦄ → ¬ (ix' ≡ ix) → ix' ↦ε, h ∌ ix
    v∌ : {ix ix' : Int} {h : Heap} {v : Val}
       → ⦃ _ : h ∌ ix ⦄ ⦃ _ : h ∌ ix' ⦄ → ¬ (ix' ≡ ix) → ix' ↦ v , h ∌ ix

data Lookup (ix : Int) (h : Heap) : Maybe Val → Dec (h ∌ ix) → Set where
  isn : ⦃ p : h ∌ ix ⦄ → Lookup ix h nothing (yes p)
  isε : ⦃ p : ¬ (h ∌ ix) ⦄ → Lookup ix h nothing (no p)
  isval : (v : Val) → ⦃ p : ¬ (h ∌ ix) ⦄ → Lookup ix h (just v) (no p)

lookupHeap : (ix : Int) → (h : Heap) → Σ (Maybe Val) (λ v → Σ (Dec (h ∌ ix)) (λ p → Lookup ix h v p))
lookupHeap ix ∅ = nothing , yes ∅∌ , isn
lookupHeap ix (ix' ↦ε, h) with ix == ix'
... | yes refl = nothing , no (λ { (ε∌ ix≢ix) → ix≢ix refl }) , isε
... | no ix≢ix' with lookupHeap ix h
... | (.nothing , .(yes _) , isn) = nothing , yes (ε∌ λ { ix'≡ix → ix≢ix' (sym ix'≡ix) }) , isn
... | (.nothing , .(no ¬h∌ix) , isε ⦃ ¬h∌ix ⦄) = nothing , no (λ { (ε∌ ix'≢ix) → {!!} }) , isε
... | (.(just v) , .(no ¬h∌ix) , isval v ⦃ ¬h∌ix ⦄) = just v , no (λ { (ε∌ ix'≢ix) → {!!} }) , isval v
lookupHeap ix (ix' ↦ v , h) with ix == ix'
... | yes refl = just v , no (λ { (v∌ ix≢ix) → ix≢ix refl }) , isval v
... | no ix≢ix' with lookupHeap ix h
... | (.nothing , .(yes _) , isn) = nothing , yes (v∌ (λ { ix'≡ix → ix≢ix' (sym ix'≡ix) })) , isn
... | (.nothing , .(no ¬h∌ix) , isε ⦃ ¬h∌ix ⦄) = nothing , no (λ { (v∌ ix'≢ix) → {!!} }) , isε
... | (.(just w) , .(no ¬h∌ix) , isval w ⦃ ¬h∌ix ⦄) = just w , no (λ { (v∌ ix'≢ix) → {!!} }) , isval w

infix 2 _≤ₕ_

data _≤ₕ_ : Heap → Heap → Set where
  h≤h : {h : Heap} → h ≤ₕ h
  h≤ε : {h : Heap} {ix : Int} ⦃ p : h ∌ ix ⦄
      → h ≤ₕ ix ↦ε, h
  h≤v : {h : Heap} {ix : Int} {v : Val} ⦃ p : h ∌ ix ⦄
      → h ≤ₕ ix ↦ v , h
  ε≤v : {h : Heap} {ix : Int} {v : Val} ⦃ p : h ∌ ix ⦄
      → ix ↦ε, h ≤ₕ ix ↦ v , h
  h≤s : {h₁ h₂ : Heap} {ix : Int} {v w : Val} ⦃ p₁ : h₁ ∌ ix ⦄ ⦃ p₂ : h₂ ∌ ix ⦄
      → h₁ ≤ₕ h₂ → v ≤ w → ix ↦ v , h₁ ≤ₕ ix ↦ w , h₂

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
  case lookupHeap ix heap of
    λ { (nothing , p) → return (others , insertWith _++_ ix [ k ] blkd , cntr , heap)
      ; (just v  , p) → return (k v ∷ others , blkd , cntr , heap) }
step (Put (ivar ix) v t₂ , others) blkd cntr heap =
  case lookupHeap ix heap of
    λ { (.nothing , .(yes _) , isn) → case find ix blkd of
        λ { nothing → return (t₂ ∷ others , blkd , cntr , (ix ↦ v , heap))
          ; (just ls) → return (t₂ ∷ map (λ k → k v) ls ++ others , remove ix blkd , cntr , heap) }
      ; (.nothing , .(no _) , isε) → {!!}
      ; (.(just v) , .(no _) , isval v) → {!!} }

    -- λ { (nothing , yes p) → case find ix blkd of
    --     λ { nothing → return (t₂ ∷ others , blkd , cntr , (ix ↦ v , heap) ⦃ p = p ⦄)
    --       ; (just ls) → return (t₂ ∷ map (λ k → k v) ls ++ others , remove ix blkd , cntr , heap) }
    --   ; (nothing , no p) → {!!}
    --   ; (just v₀ , yes p) → {!!}
    --   ; (just v₀ , no p) → {!!} }

    -- λ { nothing → case find ix blkd of
    --     λ { nothing → return (t₂ ∷ others , blkd , cntr , ix ↦ v , {!!})
    --       ; (just ls) → {!!} }
    --   ; (just v) → {!!} }
  -- let heap' = ix ↦ v , heap
  -- in case (lookupHeap ix heap) of
  --     λ { nothing → case find ix blkd of
  --       λ { nothing → return (t₂ ∷ others , blkd , cntr , heap')
  --         ; (just ls) → return (t₂ ∷ map (λ k → k v) ls ++ others , remove ix blkd , cntr , heap) }
  --       ; (just v₀) → left (MultiplePut v ix v₀) }
step (New k , others) blkd cntr heap =
  {!!}
  -- return (k (ivar cntr) ∷ others , blkd , cntr + 1 , cntr ↦ε, heap)
step (Fork t₁ t₂ , others) blkd cntr heap =
  return (t₁ ∷ t₂ ∷ others , blkd , cntr , heap)
step (Done , others) blkd cntr heap =
  return (others , blkd , cntr , heap)

-- monotonicity : ∀ {threads} {blkd} {cntr} {heap}
--              → ∀ {threads'} {blkd'} {cntr'} {heap'}
--              → step threads blkd cntr heap ≡ right (threads' , blkd' , cntr' , heap')
--              → heap ≤ₕ heap'
-- monotonicity {Get (ivar ix) k , others} {heap = heap} p with (lookupHeap ix heap)
-- monotonicity {Get (ivar ix) k , others} p | q = {!!}
-- monotonicity {Put (ivar ix) v t₂ , others} {heap = heap} p with (lookupHeap ix heap)
-- monotonicity {Put (ivar ix) v t₂ , others} {blkd = blkd} p | q = {!!}
-- monotonicity {New k , others} p = {!!}
-- monotonicity {Fork t₁ t₂ , others} p = {!!}
-- monotonicity {Done , others} p = {!!}
