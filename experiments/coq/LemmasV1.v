Require Import Coq.omega.Omega.

Require Import SimpleParV1.
Require Import Utils.
Require Import Par.Tactics.

Definition steps (trc : Trace) (others : list Trace)
           (blkd : Pool) (cntr : nat) (heap : Heap) : Prop :=
  exists trcs blkd' cntr' heap',
    step trc others blkd cntr heap = inr (trcs, blkd', cntr', heap').

Lemma steps_cntr (trc : Trace) (others : list Trace)
      (blkd : Pool) (cntr : nat) (heap : Heap) :
  forall trcs blkd' cntr' heap',
    step trc others blkd cntr heap = inr (trcs, blkd', cntr', heap') ->
    cntr <= cntr'.
Proof.
  intros.
  induction trc;
    invert H; destructo; inverto; auto || omega.
Qed.

Lemma monotonicity_step (trc : Trace) (others : list Trace)
      (blkd : Pool) (cntr : nat) (heap : Heap) :
  forall trcs blkd' cntr' heap',
    step trc others blkd cntr heap = inr (trcs, blkd', cntr', heap') ->
    heap <<= heap'.
Proof.
  intros.
  induction trc;
    invert H; destructo; inverto; auto.
Qed.

Hint Resolve monotonicity_step.

Lemma monotonicity_sched (fuel : nat) :
  forall randoms threads blkd cntr heap heap',
    sched fuel randoms threads blkd cntr heap = inr heap' ->
    heap <<= heap'.
Proof.
  intros. destruct fuel.
  - invert H.
  - invert H. destruct threads.
    + destruct_if.
      * invert_sum. auto.
      * invert_sum.
    + destruct randoms.
      destruct (yank n t threads).
      destruct (step t0 l blkd cntr heap).
      * invert_sum.
      * repeat destruct p.
        (* Can't do induction using randoms *)
Abort.
