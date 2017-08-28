Require Export Coq.Structures.OrderedTypeEx.

Definition Val := nat.

Module Val_as_OT := Nat_as_OT.

Require Import Utils.

Module OV_as_OT := option_as_OT Val_as_OT.
