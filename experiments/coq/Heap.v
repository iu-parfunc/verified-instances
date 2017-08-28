Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.

Require Import Trace.

Module H := FMapList.Make_ord Nat_as_OT OV_as_OT.
Module HM := H.MapS.

Definition Heap := H.t.

Module M := FMapList.Make (Nat_as_OT).

Definition add_with {A} (f : A -> A -> A) (key : nat) (new_val : A) (m : M.t A) : M.t A :=
  match M.find key m with
  | None => M.add key new_val m
  | Some old_val => M.add key (f new_val old_val) m
  end.

Definition singleton {A} (key : nat) (val : A) : HM.t A :=
  HM.add key val (HM.empty A).

Definition Pool := M.t (list (Val -> Trace)).

(* heap_lteq h1 h2 = H.lt h1 h2 /\ H.eq h1 h2 *)
(* heap_lteq h1 h2 = ~ H.lt h2 h1 *)

Reserved Notation "h1 <<= h2" (at level 40).

Inductive heap_lteq : Heap -> Heap -> Prop :=
  heap_refl : forall h, h <<= h
| heap_add_none : forall h k, h <<= HM.add k None h
| heap_add_some : forall h k v, h <<= HM.add k (Some v) h
| heap_trans : forall h1 h2 h3, h1 <<= h2 -> h2 <<= h3 -> h1 <<= h3
where "h1 <<= h2" := (heap_lteq h1 h2).

Hint Constructors heap_lteq.
