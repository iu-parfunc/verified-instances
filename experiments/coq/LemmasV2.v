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

Require Import Coq.Program.Equality.

Lemma monotonicity_sched :
  forall randoms threads blkd cntr heap heap',
    sched randoms threads blkd cntr heap = inr heap' ->
    heap <<= heap'.
Proof.
  (* This is a gnarly proof but automation makes it look simple *)
  intros.
  dependent induction randoms;
    invert H; destructo; inverto; eauto using monotonicity_step.
Qed.

Lemma deterministic_runPar_nil :
  forall p randoms v1 v2,
    runPar nil p = inr v1 ->
    runPar randoms p = inr v2 ->
    v1 = v2.
Proof.
  intros. cbv in H. inverto.
Qed.

Conjecture heap_find_0 : forall h,
    singleton 0 None <<= h -> HM.find 0 h = Some None.

Theorem deterministic_runPar :
  forall randoms1 randoms2 p v1 v2,
    runPar randoms1 p = inr v1 ->
    runPar randoms2 p = inr v2 ->
    v1 = v2.
Proof.
  intros. destruct p.
  induction (t (fun v => Put 0 v Done));
    unfold runPar in H; simpl in H.
  destructo; inverto.
  - unfold id in *; subst.
    apply monotonicity_sched in Heqs.
    apply heap_find_0 in Heqs.
    rewrite Heqs in Heqo0. inverto.
  - auto.
  - auto using H1.
  - auto.
  - destructo; inverto.
    unfold id in *; subst.
    apply monotonicity_sched in Heqs.
    apply heap_find_0 in Heqs.
    rewrite Heqs in Heqo0; inverto.
Qed.

Print Assumptions deterministic_runPar.
