Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Require Import Future.
Require Import IVar.
Require Import Heap2.
Require Import Tactics.

Definition FiniteHeap (A : Type) : Type := list (IVar A * A).

Definition initFiniteHeap {A} : FiniteHeap A := nil.

Definition newFiniteHeap {A} (k : IVar A -> Future (FiniteHeap A)) : Future (FiniteHeap A) := k 0.

Definition writeFiniteHeap {A} (i : IVar A) (v : A) (h : FiniteHeap A) : Future (FiniteHeap A) :=
  retFuture (cons (i , v) h).

Fixpoint readFiniteHeap {A} (i : IVar A) (h : FiniteHeap A) : Future A :=
  match h with
  | [] => failFuture "not found"
  | cons (j , a) h' => if j =? i then retFuture a else readFiniteHeap i h'
  end.

Fixpoint maxIVar {A} (h : FiniteHeap A) : IVar A :=
  match h with
  | [] => 0
  | cons (i , a) h' => let j := maxIVar h' in if i <? j then j else i
  end.

Definition splitFiniteHeap {A} (h : FiniteHeap A) : FiniteHeap A * FiniteHeap A :=
  let max := maxIVar h / 2 in
  partition (fun a => fst a <? max) h.

Definition joinFiniteHeap {A} (h1 h2 : FiniteHeap A) : Future (FiniteHeap A) :=
  retFuture (h1 ++ h2).

Definition dropFiniteHeap {A} (h : FiniteHeap A) : unit := tt.

Lemma commutesFiniteHeap : forall {A} {i1 i2 : IVar A} {v1 v2 : A} {k : FiniteHeap A -> Future (FiniteHeap A)} {h : FiniteHeap A},
    bindFuture (writeFiniteHeap i2 v2 h) (fun h' => bindFuture (writeFiniteHeap i1 v1 h') k) =
    bindFuture (writeFiniteHeap i1 v1 h) (fun h' => bindFuture (writeFiniteHeap i2 v2 h') k) /\
    bindFuture (writeFiniteHeap i1 v1 h) (fun h' => bindFuture (writeFiniteHeap i2 v2 h') k) =
    let (h1, h2) := splitFiniteHeap h
    in bindFuture (writeFiniteHeap i1 v1 h) (fun h' => bindFuture (writeFiniteHeap i2 v2 h) (fun h'' => bindFuture (joinFiniteHeap h' h'') k)).
Proof.
  intros.
  unfold bindFuture.
  destructo.
Admitted.
