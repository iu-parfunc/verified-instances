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
