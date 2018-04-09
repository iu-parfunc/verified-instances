Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Val.
Require Import IVar.
Require Import Trace.

Module Type Heap.
  Parameter Heap : Type -> Type.
  Axiom newHeap : forall {A}, (IVar A -> Heap A) -> Heap A.
  Axiom writeHeap : forall {A}, IVar A -> A -> Heap A -> Heap A.
  Axiom readHeap : forall {A}, IVar A -> Heap A -> A.
  Axiom splitHeap : forall {A}, Heap A -> Heap A * Heap A.
  Axiom joinHeap : forall {A}, Heap A -> Heap A -> Heap A.
  Axiom dropHeap : forall {A}, Heap A -> unit.
  Axiom commutesHeap : forall {A} (h : Heap A) (f g : Heap A -> Heap A),
      f (g h) = g (f h) /\ g (f h) = let (h1, h2) := splitHeap h in joinHeap (f h) (g h).
End Heap.

Module Par (H : Heap).
  Import H.

  Definition new {A} (k : IVar A -> Heap A) : Heap A :=
    newHeap k.

  Definition get {A} (i : IVar A) (k : A -> Heap A -> Heap A) (h : Heap A) : Heap A :=
    k (readHeap i h) h.

  Definition put {A} (i : IVar A) (v : A) (k : Heap A -> Heap A) (h : Heap A) : Heap A :=
    k (writeHeap i v h).

  Lemma putsCommute {A} (i1 i2 : IVar A) (v1 v2 : A) (k : Heap A -> Heap A) :
    put i2 v2 (fun h => put i1 v1 k h) = put i1 v1 (fun h => put i2 v2 k h).
  Proof.
    compute.
    extensionality h.
    assert (writeHeap i2 v2 (writeHeap i1 v1 h) = writeHeap i1 v1 (writeHeap i2 v2 h)).
    apply (commutesHeap h (writeHeap i2 v2) (writeHeap i1 v1)).
    congruence.
  Qed.

  Definition fork {A} (k1 k2 : Heap A -> Heap A) (h : Heap A) : Heap A :=
    let (h1, h2) := splitHeap h in joinHeap (k1 h) (k2 h).

  Fixpoint runTrace (tr : Trace) (h : Heap Val) : Heap Val :=
    match tr with
    | Get i k => get i (fun v h' => runTrace (k v) h') h
    | Put i v tr1 => put i v (fun h' => runTrace tr1 h') h
    | New k => new (fun i => runTrace (k i) h)
    | Fork tr1 tr2 => fork (runTrace tr1) (runTrace tr2) h
    | Done => h
    end.

End Par.
