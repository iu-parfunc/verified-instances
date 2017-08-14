Require Import Coq.omega.Omega.

Require Import SimpleParV2.
Require Import Utils.
Require Import Par.Tactics.

Definition steps trc others blkd cntr heap : Prop :=
  exists trcs blkd' cntr' heap',
    step trc others blkd cntr heap = inr (trcs, blkd', cntr', heap').

Lemma steps_cntr trc others blkd cntr heap :
  forall trcs blkd' cntr' heap',
    step trc others blkd cntr heap = inr (trcs, blkd', cntr', heap') ->
    cntr <= cntr'.
Proof.
  intros.
  induction trc;
    invert H; destructo; invert_inlr; auto || omega.
Qed.

Lemma monotonicity_step (trc : Trace) (others : list Trace)
      (blkd : Pool) (cntr : nat) (heap : Heap) :
  forall trcs blkd' cntr' heap',
    step trc others blkd cntr heap = inr (trcs, blkd', cntr', heap') ->
    heap <<= heap'.
Proof.
  intros.
  induction trc;
    invert H; destructo; invert_inlr; auto.
Qed.

Hint Resolve monotonicity_step.

Require Import Coq.Program.Equality.

Lemma monotonicity_sched :
  forall randoms threads blkd cntr heap heap',
    sched randoms threads blkd cntr heap = inr heap' ->
    heap <<= heap'.
Proof.
  (* This is a gnarly proof but automation makes it look simple *)
  intros.
  dependent induction randoms;
    invert H; destructo; invert_inlr; eauto.
Qed.
