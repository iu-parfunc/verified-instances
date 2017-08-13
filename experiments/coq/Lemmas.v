Require Import Par.SimplePar.
Require Import Omega.

Definition steps (trc : Trace) (others : list Trace)
           (blkd : Pool) (cntr : nat) (heap : Heap) : Prop :=
  exists trcs blkd' cntr' heap',
    step trc others blkd cntr heap = inr (trcs, blkd', cntr', heap').

Ltac destructo :=
  repeat
    match goal with
    | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
      match type of X with
      | option _ => destruct X
      end
    end.

Ltac invert H :=
  inversion H; subst; clear H.

Ltac invert_inlr :=
  repeat
    match goal with
    | [ H : inl _ = inl _ |- _ ] => invert H
    | [ H : inl _ = inr _ |- _ ] => invert H
    | [ H : inr _ = inl _ |- _ ] => invert H
    | [ H : inr _ = inr _ |- _ ] => invert H
    end.

Lemma steps_cntr (trc : Trace) (others : list Trace)
      (blkd : Pool) (cntr : nat) (heap : Heap) :
  forall trcs blkd' cntr' heap',
    step trc others blkd cntr heap = inr (trcs, blkd', cntr', heap') ->
    cntr <= cntr'.
Proof.
  intros.
  induction trc;
    inversion H; destructo; invert_inlr; auto || omega.
Qed.

(* heap_lteq h1 h2 = H.lt h1 h2 /\ H.eq h1 h2 *)
(* heap_lteq h1 h2 = ~ H.lt h2 h1 *)

Inductive heap_lteq : Heap -> Heap -> Prop :=
  heap_refl : forall h, h <= h
| heap_add_none : forall h k, h <= HM.add k None h
| heap_add_some : forall h k v, h <= HM.add k (Some v) h
where "h1 <= h2" := (heap_lteq h1 h2).

Hint Constructors heap_lteq.

Lemma monotonicity (trc : Trace) (others : list Trace)
      (blkd : Pool) (cntr : nat) (heap : Heap) :
  forall trcs blkd' cntr' heap',
    step trc others blkd cntr heap = inr (trcs, blkd', cntr', heap') ->
    heap <= heap'.
Proof.
  intros.
  induction trc;
    inversion H; destructo; invert_inlr; auto.
Qed.
