Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.

Definition IVar (A : Type) := nat.

Module IVar_as_OT <: OrderedType.
  Parameter A : Type.
  Definition t := IVar A.
  Definition eq := Nat_as_OT.eq.
  Definition eq_refl := Nat_as_OT.eq_refl.
  Definition eq_sym := Nat_as_OT.eq_sym.
  Definition eq_trans := Nat_as_OT.eq_trans.
  Definition lt := Nat_as_OT.lt.
  Definition lt_trans := Nat_as_OT.lt_trans.
  Definition lt_not_eq := Nat_as_OT.lt_not_eq.
  Definition compare := Nat_as_OT.compare.
  Definition eq_dec := Nat_as_OT.eq_dec.
End IVar_as_OT.
