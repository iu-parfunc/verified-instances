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
  intros. cbn in H. inverto.
Qed.

Require Import Coq.Lists.List.
Import ListNotations.

Lemma deterministic_runPar_singleton :
  forall p rnd randoms v1 v2,
    runPar [rnd] p = inr v1 ->
    runPar randoms p = inr v2 ->
    v1 = v2.
Proof.
  intros. cbn in H.
  destructo; inverto.

  - unfold step in Heqs0.
    destruct (Par.runCont p (fun v => Put 0 v Done)) eqn:?.

    + destructo.
      ++ cbn in Heqo0. inverto.
      ++ cbn in Heqs0. inverto. cbn in Heqo. inverto.

    + destructo.
      ++ cbn in Heqo0. inverto.
      ++ cbn in Heqo1. inverto.
      ++ cbn in Heqs0. inverto. cbn in Heqo.
         destruct (Nat_as_OT.compare 0 i).
         * inverto.
         * invert e. inverto. cbn in Heqo1, Heqo0.
           destruct p. cbn in Heqt.
           admit.
         * inverto.

    + cbn in Heqs0. inverto.
      cbn in Heqo. inverto.

    + cbn in Heqs0. inverto.
      cbn in Heqo. inverto.

    + cbn in Heqs0. inverto.
      cbn in Heqo. inverto.
Admitted.

Module scratch.

Example t : (Val -> Trace) -> Trace := fun f => Put 0 42 (Put 0 43 Done).
Example randoms := [3].

Eval cbn in sched randoms (Get 0 (fun v => Done) :: nil) (M.empty _) 0
                  (HM.empty _).

Eval cbn in sched randoms (t (fun v => Put 0 v Done) :: nil) (M.empty _) 1
                  (HM.empty _).

Eval cbn in step ((fun v => Put 0 10 Done) (fun v => Put 0 v Done))
                 nil (M.empty (list (Val -> Trace))) 1
                 (HM.empty _).

Eval cbn in step (Put 1 42 Done) [] (M.empty (list (Val -> Trace))) 1
                 (HM.add 0 42 (HM.empty _)).

End scratch.

Conjecture heap_lookup_eq :
  forall {V} h k (v : V),
    HM.find k (HM.add k v h) = Some v.

Conjecture heap_lookup_neq :
  forall {V} h k1 k2 (v : V),
    k1 <> k2 ->
    HM.find k1 (HM.add k2 v h) = HM.find k1 h.

Hint Resolve heap_lookup_eq heap_lookup_neq.

Theorem deterministic_runPar :
  forall randoms1 randoms2 p v1 v2,
    runPar randoms1 p = inr v1 ->
    runPar randoms2 p = inr v2 ->
    v1 = v2.
Proof.
  intros.
  induction randoms1.

  - cbn in H. inverto.

  - cbn in H. destructo; inverto.

    + apply monotonicity_step in Heqs0.
      apply monotonicity_sched in Heqs.

Admitted.

Print Assumptions deterministic_runPar.
