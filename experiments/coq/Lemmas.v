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
    | [ |- context [ match ?X with _ => _ end ] ] =>
      match type of X with
      | option _ => destruct X
      end
    end.

Ltac destruct_if :=
  repeat
    match goal with
    | [ H : context [ if ?X then _ else _ ] |- _ ] => destruct X
    | [ |- context [ if ?X then _ else _ ] ] => destruct X
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
    invert H; destructo; invert_inlr; auto || omega.
Qed.

(* heap_lteq h1 h2 = H.lt h1 h2 /\ H.eq h1 h2 *)
(* heap_lteq h1 h2 = ~ H.lt h2 h1 *)

Inductive heap_lteq : Heap -> Heap -> Prop :=
  heap_refl : forall h, h <= h
| heap_add_none : forall h k, h <= HM.add k None h
| heap_add_some : forall h k v, h <= HM.add k (Some v) h
where "h1 <= h2" := (heap_lteq h1 h2).

Hint Constructors heap_lteq.

Lemma monotonicity_step (trc : Trace) (others : list Trace)
      (blkd : Pool) (cntr : nat) (heap : Heap) :
  forall trcs blkd' cntr' heap',
    step trc others blkd cntr heap = inr (trcs, blkd', cntr', heap') ->
    heap <= heap'.
Proof.
  intros.
  induction trc;
    invert H; destructo; invert_inlr; auto.
Qed.

Hint Resolve monotonicity_step.

Lemma monotonicity_sched (fuel : nat) :
  forall randoms threads blkd cntr heap heap',
    sched fuel randoms threads blkd cntr heap = inr heap' ->
    heap <= heap'.
Proof.
  intros. destruct fuel.
  - invert H.
  - invert H. destruct threads.
    + destruct_if.
      * invert_inlr. auto.
      * invert_inlr.
    + destruct randoms.
      destruct (yank n t threads).
      destruct (step t0 l blkd cntr heap).
      * invert_inlr.
      * repeat destruct p.
        (* Can't do induction using randoms *)
Abort.
