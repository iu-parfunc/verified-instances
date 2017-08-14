Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Monads.
Require Import Coq.Structures.OrderedType.

Import ListNotations.

Polymorphic Definition joinM@{d c}
            {m : Type@{d} -> Type@{c}}
            {M : Monad m}
            {A : Type@{d}} (aMM:m (m A)) : m A :=
  bind aMM id.

Fixpoint split_at {A} (n : nat) (xs : list A) : list A * list A :=
  match (n, xs) with
  | (O, xs) => (nil, xs)
  | (S m, nil) => (nil, nil)
  | (S m, x :: xs) => let (xs1, xs2) := split_at m xs in (x :: xs1, xs2)
  end.

Definition yank {A} (n : nat) (x : A) (xs : list A) : A * list A :=
  match split_at (length (x :: xs) / n) (x :: xs) with
  | (hd, nil) => (x, hd)
  | (hd, cons x tl) => (x, hd ++ tl)
  end.

Require Import Tactics.

Module option_as_OT (A : OrderedType) <: OrderedType.
  Module OA := OrderedTypeFacts A.
  Definition t:= option A.t.
  Definition eq x y :=
    match (x, y) with
    | (None, None) => True
    | (None, Some y) => False
    | (Some x, None) => False
    | (Some x, Some y) => A.eq x y
    end.
  Hint Unfold eq.
  Ltac crush_eq :=
    repeat
      match goal with
      | [ H : t |- _] => destruct H
      | [ H : eq None (Some _) |- _] => inversion H
      | [ H : eq (Some _) None |- _] => inversion H
      | _ => eauto
      end.
  Definition eq_refl : forall x : t, eq x x.
    intros; crush_eq.
  Qed.
  Definition eq_sym : forall x y : t, eq x y -> eq y x.
    intros; crush_eq.
  Qed.
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    intros; crush_eq.
  Qed.
  Definition lt (x y : t) :=
    match (x, y) with
    | (None, None) => False
    | (None, Some y) => True
    | (Some x, None) => False
    | (Some x, Some y) => A.lt x y
    end.
  Hint Unfold lt.
  Ltac crush_lt :=
    repeat match goal with
           | [ H : t |- _] => destruct H
           | [ H : lt (Some _) None |- _] => inversion H
           | [ H : eq (Some _) None |- _] => inversion H
           | [ H : eq None (Some _) |- _] => inversion H
           | [ H : lt _ _ |- ~ _] => eapply A.lt_not_eq in H
           | [ |- Compare _ _ None None] => eapply EQ
           | [ |- Compare _ _ None (Some _)] => eapply LT
           | [ |- Compare _ _ (Some _) None] => eapply GT
           | [ H : A.lt ?X ?Y |- Compare _ _ (Some ?X) (Some ?Y)] => eapply LT
           | [ H : A.eq ?X ?Y |- Compare _ _ (Some ?X) (Some ?Y)] => eapply EQ
           | [ H : A.lt ?Y ?X |- Compare _ _ (Some ?X) (Some ?Y)] => eapply GT
           | [ |- {eq ?X ?Y} + {~ eq ?X ?Y}] => unfold eq
           | [ |- {A.eq ?X ?Y} + {~ A.eq ?X ?Y}] => eapply A.eq_dec
           | _ => eauto
           end.
  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    intros; crush_lt.
  Qed.
  Definition lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    intros; crush_lt.
  Qed.
  Definition compare : forall x y : t, Compare lt eq x y.
    intros [x|] [y|]. destruct (A.compare x y).
    all: crush_lt.
  Qed.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    intros; crush_lt.
  Qed.
End option_as_OT.
