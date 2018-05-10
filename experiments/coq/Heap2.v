Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

Require Import Val.
Require Import IVar.
Require Import Trace.
Require Import Par.
Require Import Future.
Require Import Tactics.

Module Type Heap.
  Parameter Heap : Type -> Type.
  Axiom initHeap : forall {A}, Heap A.
  Axiom newHeap : forall {A}, (IVar A -> Future (Heap A)) -> Future (Heap A).
  Axiom writeHeap : forall {A}, IVar A -> A -> Heap A -> Future (Heap A).
  Axiom readHeap : forall {A}, IVar A -> Heap A -> Future A.
  Axiom splitHeap : forall {A}, Heap A -> Heap A * Heap A.
  Axiom joinHeap : forall {A}, Heap A -> Heap A -> Future (Heap A).
  Axiom dropHeap : forall {A}, Heap A -> unit.
  Axiom commutesHeap : forall {A} {i1 i2 : IVar A} {v1 v2 : A} {k : Heap A -> Future (Heap A)} {h : Heap A},
      bindFuture (writeHeap i2 v2 h) (fun h' => bindFuture (writeHeap i1 v1 h') k) =
      bindFuture (writeHeap i1 v1 h) (fun h' => bindFuture (writeHeap i2 v2 h') k) /\
      bindFuture (writeHeap i1 v1 h) (fun h' => bindFuture (writeHeap i2 v2 h') k) =
      let (h1, h2) := splitHeap h
      in bindFuture (writeHeap i1 v1 h) (fun h' => bindFuture (writeHeap i2 v2 h) (fun h'' => bindFuture (joinHeap h' h'') k)).
End Heap.

Module Par (H : Heap).
  Import H.

  Definition new {A} (k : IVar A -> Future (Heap A)) : Future (Heap A) :=
    newHeap k.

  Definition get {A} (i : IVar A) (k : A -> Heap A -> Future (Heap A)) (h : Heap A) : Future (Heap A) :=
    bindFuture (readHeap i h) (fun a => k a h).

  Definition put {A} (i : IVar A) (v : A) (k : Heap A -> Future (Heap A)) (h : Heap A) : Future (Heap A) :=
    bindFuture (writeHeap i v h) k.

  Lemma putsCommute {A} (i1 i2 : IVar A) (v1 v2 : A) (k : Heap A -> Future (Heap A)) :
    put i2 v2 (fun h => put i1 v1 k h) = put i1 v1 (fun h => put i2 v2 k h).
  Proof.
    unfold put.
    extensionality h.
    apply commutesHeap.
  Qed.

  Definition fork {A} (k1 k2 : Heap A -> Heap A) (h : Heap A) : Future (Heap A) :=
    let (h1, h2) := splitHeap h in joinHeap (k1 h) (k2 h).

  Fixpoint step (tr : Trace) (h : Heap Val) : Future (Heap Val) :=
    match tr with
    | Get i k => get i (fun v h' => step (k v) h') h
    | Put i v tr1 => put i v (fun h' => step tr1 h') h
    | New k => new (fun i => step (k i) h)
    | Fork tr1 tr2 => bindFuture (step tr1 h) (fun h' => step tr2 h')
    | Done => retFuture h
    end.

  Fixpoint sched (thunks : list Trace) (h : Heap Val) : Future (Heap Val) :=
    match thunks with
    | nil => retFuture h
    | t :: ts => bindFuture (step t h) (sched ts)
    end.

  Definition runPar (p : Par Val) : Future Val :=
    let initThreads := [ runCont p (fun v => Put 0 v Done) ] in
    let finalHeap := sched initThreads initHeap in
    bindFuture finalHeap (fun h => readHeap 0 h)
  .

  Lemma sched_two_deterministic : forall {t1 t2 : Trace} {h : Heap Val},
      sched (t1 :: t2 :: []) h = sched (t2 :: t1 :: []) h.
  Proof.
    intros.
    induction t1; induction t2; compute.
  Abort.

End Par.
