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

Module scratch.

Example t : (Val -> Trace) -> Trace := fun f => Put 0 42 (Put 0 43 Done).
Example randoms := [3].

Eval cbn in sched randoms (Get 0 (fun v => Done) :: nil) (M.empty _) 0
                  (singleton 0 None).

Eval cbn in sched randoms (t (fun v => Put 0 v Done) :: nil) (M.empty _) 1
                  (singleton 0 None).

Conjecture heap_find_0 : forall h,
    singleton 0 None <<= h -> HM.find 0 h = Some None.

Eval cbn in step ((fun v => Put 0 10 Done) (fun v => Put 0 v Done))
                 nil (M.empty (list (Val -> Trace))) 1
                 (singleton 0 None).


Eval cbn in step (Put 1 42 Done) [] (M.empty (list (Val -> Trace))) 1
                 (HM.add 0 (Some 42) (singleton 0 None)).

End scratch.

Conjecture heap_lookup_eq :
  forall {V} h k (v : V),
    HM.find k (HM.add k v h) = Some v.

Conjecture heap_lookup_neq :
  forall {V} h k1 k2 (v : V),
    k1 <> k2 ->
    HM.find k1 (HM.add k2 v h) = HM.find k1 h.

Hint Resolve heap_lookup_eq heap_lookup_neq.

Lemma step_heap_0 :
  forall t n v h h' ts p n',
    step t [] (M.empty _) n (HM.add 0 v h) = inr (ts, p, n', h') ->
    HM.find 0 h' = Some v.
Proof.
  intros.
  destruct t eqn:?; simpl in *;
    destructo; unfold id in *; subst;
      inverto; eauto.

  - destruct i. rewrite heap_lookup_eq in Heqo0. inverto.

(*   intros. *)
(*   destruct t; cbn in *; *)
(*     destructo; unfold id in *; subst; inverto; eauto. *)

(*   - destruct i; symmetry. *)
(*     -- rewrite Heqo0. admit. *)
(*     -- eapply heap_lookup_neq. auto. *)

(*   - destruct i; symmetry. *)
(*     -- admit. *)
(*     -- eapply heap_lookup_neq. auto. *)

(*   - destruct n; symmetry. *)
(*     -- admit. *)
(*     -- eapply heap_lookup_neq. auto. *)
(* Admitted. *)

Lemma sched_heap_0 :
  forall t randoms h n,
    sched randoms ([t (fun v => Put 0 v Done)]) (M.empty _) n
          (singleton 0 None) = inr h ->
    exists v, HM.find 0 h = Some v.
Proof.
  intros. induction randoms; cbn in *.

  + inverto. cbn. eauto.
  + destructo.
    ++ inverto.
    ++ destruct (t (fun v => Put 0 v Done)) eqn:?; cbn in *;
         destructo; unfold id in *; subst;
           try destruct (Nat_as_OT.compare i 0); inverto.

  - invert e.
    eapply IHrandoms. clear IHrandoms.
    unfold sched.
    destruct randoms; destructo; cbn in *; inverto.

  - invert l0.

  - invert l0.
    eapply IHrandoms. clear IHrandoms.
    unfold sched.
    destruct randoms; destructo; cbn in *; inverto.

  - eapply IHrandoms. clear IHrandoms.
    unfold sched.
    destruct randoms; destructo; cbn in *; inverto.

  - invert e.
    eapply IHrandoms. clear IHrandoms.
    unfold sched.
    destruct randoms; destructo; cbn in *; inverto.
    f_equal. admit.
    inverto.
    admit.

  - invert Heqp.
    destructo; cbn in *; inverto.



Theorem deterministic_runPar :
  forall randoms1 randoms2 p v1 v2,
    runPar randoms1 p = inr v1 ->
    runPar randoms2 p = inr v2 ->
    v1 = v2.
Proof.

  intros. destruct p.

  unfold runPar in H. cbn in *.
  destructo; inverto.

  unfold id in *. subst.

  destruct (t0 (fun v : Val => Put 0 v Done)) eqn:?; cbn in *.

  - induction randoms1.

    + invert Heqs0. cbn in Heqo2. inverto.
    + unfold sched in Heqs0. destructo. cbn in *. destructo.
      ++ inverto.
      ++ invert Heqp. cbn in Heqs1. destructo. unfold id in *. subst.
         inverto.
         destruct (Nat_as_OT.compare i 0); inverto.
         destruct (Nat_as_OT.compare i 0); inverto.
         destruct (Nat_as_OT.compare i 0); inverto.
         invert e.

  (* intros. destruct p. unfold runPar in H. simpl in *. *)
  (* destructo; inverto. *)

  (* unfold id in *; subst. *)
  (* (* unfold sched in Heqs. *) *)

  (* dependent induction randoms1; cbn in *. *)

  (* - invert Heqs. compute in Heqo0. inverto. *)

  (* - destructo; inverto. *)
  (*   induction (t0 (fun v => Put 0 v Done)) eqn:?; cbn in *. *)

  (*   + eapply H. *)
  (*   + auto. *)
  (*   + auto using H. *)
  (*   + auto. *)
  (*   + unfold id in *; subst. *)


  (* induction randoms1. *)
  (* - destructo; simpl in *. invert Heqs. *)
  (*   compute in Heqo0. inverto. *)
  (* - inverto. *)
  (* - simpl in *. destructo; inverto. *)
  (*   apply IHrandoms1. clear IHrandoms1. *)
  (*   rewrite <- Heqs. clear Heqs. *)
  (*   invert Heqs0. *)


  (* destruct (t (fun v => Put 0 v Done)) eqn:?; simpl in H; *)
  (*   unfold id in *; subst; destructo; inverto. *)
  (* - unfold sched in Heqs. *)
  (*   induction randoms1. *)
  (*   + destructo. invert Heqs. compute in Heqo0. inverto. *)
  (*   + inverto. *)
  (*   + destruct (yank a (t (fun v => Put 0 v Done)) nil) eqn:?. compute in Heqp. *)
  (*     invert Heqp. simpl in *. destructo; inverto. *)
  (*     apply IHrandoms1. clear IHrandoms1. *)

(*   induction (t (fun v => Put 0 v Done)) eqn:?; *)
(*     unfold runPar in H; simpl in H. *)
(*   destructo; inverto. *)
(*   - auto. *)
(*   - auto. *)
(*   - auto using H1. *)
(*   - auto. *)
(*   - destructo; inverto. *)
(*     unfold id in *; subst. *)

(*     induction randoms1. *)

(*     + invert Heqs. compute in Heqo0. inverto. *)
(*     + invert Heqs. *)
(*       ++ destructo. inverto. *)
(*       ++ apply IHrandoms1. clear IHrandoms1. *)
(*          unfold step in Heqs. *)

(*     eauto using monotonicity_sched, heap_find_0. *)
(*     apply monotonicity_sched in Heqs. *)
(*     apply heap_find_0 in Heqs. *)
(*     rewrite Heqs in Heqo0; inverto. *)
(* Qed. *)

Print Assumptions deterministic_runPar.
