Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Monads.
Require Import Coq.Structures.OrderedType.

Import ListNotations.

Require Import Par.Tactics.

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

Lemma split_at_nil : forall {A} n, @split_at A n nil = (nil, nil).
Proof.
  intros. destruct n; auto.
Qed.

Hint Resolve split_at_nil.

Lemma split_at_S_singleton : forall {A} n (x : A), split_at (S n) [x] = ([x], nil).
Proof.
  intros. destruct n; auto.
Qed.

Hint Resolve split_at_S_singleton.

Lemma split_at_length : forall {A} (xs : list A), split_at (length xs) xs = (xs, nil).
Proof.
  intros.
  induction xs; simpl in *; auto.
  destructo; congruence.
Qed.

Hint Resolve split_at_length.

Lemma length_0 : forall {A} (xs : list A), length xs = 0 -> xs = [].
Proof.
  intros.
  destruct xs.
  - auto.
  - invert H.
Qed.

Lemma nth_nil : forall {A} n x, @nth A n [] x = x.
Proof.
  intros.
  induction n; auto.
Qed.

Definition yank {A} (n : nat) (x : A) (xs : list A) : A * list A :=
  match split_at (n mod length (x :: xs)) (x :: xs) with
  | (hd, nil) => (x, hd)
  | (hd, cons x tl) => (x, hd ++ tl)
  end.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Conjecture yank_fst : forall {A} n x xs,
    n < length (x :: xs) -> fst (@yank A (S n) x xs) = nth n xs x.
QuickChick yank_fst.

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
