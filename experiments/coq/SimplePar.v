(** * SimplePar *)

Set Asymmetric Patterns.

Require Import Coq.Arith.Arith.
Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Lists.Streams.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.ListMonad.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Monads.EitherMonad.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

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

Definition Val := nat.

Module Val_as_OT := Nat_as_OT.

Definition IVar (A : Type) := nat.

Module IVar_as_OT <: OrderedType.
  Parameter A : Type.
  Definition t := IVar A.
  Definition eq := Nat_as_OT.eq.
  Definition eq_refl := Nat_as_OT.eq_refl.
  Definition eq_sym := Nat_as_OT.eq_sym.
  Definition eq_trans := Nat_as_OT.eq_trans.
  Definition lt := Nat_as_OT.lt.
  Definition lt_trans := Nat_as_OT.lt_trans.
  Definition lt_not_eq := Nat_as_OT.lt_not_eq.
  Definition compare := Nat_as_OT.compare.
  Definition eq_dec := Nat_as_OT.eq_dec.
End IVar_as_OT.

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
    repeat match goal with
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

Inductive Trace : Type :=
  Get  : IVar Val -> (Val -> Trace) -> Trace
| Put  : IVar Val -> Val -> Trace -> Trace
| New  : (IVar Val -> Trace) -> Trace
| Fork : Trace -> Trace -> Trace
| Done : Trace
.

Inductive Par {A : Type} :=
  mkPar : ((A -> Trace) -> Trace) -> Par.

Arguments Par : clear implicits.

Definition runCont {A} (p : Par A) : (A -> Trace) -> Trace :=
  match p with
  | mkPar k => k
  end.
Hint Unfold runCont.

Global Instance Functor_Par : Functor Par :=
  {| fmap := fun _ _ f p => mkPar (fun c => runCont p (compose c f)) |}.

Global Instance Applicative_Par : Applicative Par :=
  {| pure := fun _ a => mkPar (fun k => k a)
   ; ap := fun _ _ pf pa => mkPar (fun bk => runCont pa (fun a => runCont pf (fun f => bk (f a))))
  |}.

Global Instance Monad_Par : Monad Par :=
  {| ret := fun _ a => mkPar (fun k => k a)
   ; bind := fun _ _ pa k => mkPar (fun bk => runCont pa (fun a => runCont (k a) bk))
  |}.

Definition new : Par (IVar Val) :=
  mkPar New.

Definition get (v : IVar Val) : Par Val :=
  mkPar (fun c => Get v c).

Definition put (v : IVar Val) (a : Val) : Par unit :=
  mkPar (fun c => Put v a (c tt)).

Definition fork (p : Par unit) : Par unit :=
  match p with
  | mkPar k1 => mkPar (fun k2 => Fork (k1 (fun _ => Done)) (k2 tt))
  end.

Module OV_as_OT := option_as_OT Val_as_OT.

Module H := FMapList.Make_ord Nat_as_OT OV_as_OT.
Module HM := H.MapS.

Definition Heap := H.t.

Module M := FMapList.Make (Nat_as_OT).

Definition add_with {A} (f : A -> A -> A) (key : nat) (new_val : A) (m : M.t A) : M.t A :=
  match M.find key m with
  | None => M.add key new_val m
  | Some old_val => M.add key (f new_val old_val) m
  end.

Definition singleton {A} (key : nat) (val : A) : HM.t A :=
  HM.add key val (HM.empty A).

Definition Pool := M.t (list (Val -> Trace)).

Inductive Exn : Type :=
  MultiplePut : Val -> nat -> Val -> Exn
| Deadlock : M.t (list (Val -> Trace)) -> Exn
| HeapExn : Exn
| OutOfFuel : Exn
.

Definition step (trc : Trace) (others : list Trace)
           (blkd : Pool) (cntr : nat) (heap : Heap)
  : Exn + (list Trace * Pool * nat * Heap) :=
  match trc with
  | Done => ret (others, blkd, cntr, heap)
  | Fork t1 t2 => ret (t1 :: t2 :: others, blkd, cntr, heap)
  | New k => ret (k cntr :: others, blkd, cntr + 1, HM.add cntr None heap)
  | Get ix k => match joinM (HM.find ix heap) with
               | None => ret (others, add_with (app (A:=_)) ix [k] blkd, cntr, heap)
               | Some v => ret (k v :: others, blkd, cntr, heap)
               end
  | Put ix v t2 => let heap' := HM.add ix (Some v) heap in
                  match joinM (HM.find ix heap) with
                  | None => match M.find ix blkd with
                           | None => ret (t2 :: others, blkd, cntr, heap')
                           | Some ls => ret (t2 :: fmap (fun k => k v) ls ++ others, M.remove ix blkd, cntr, heap')
                           end
                  | Some v0 => inl (MultiplePut v ix v0)
                  end
  end.

Fixpoint sched (fuel : nat) (randoms : Stream nat) (threads : list Trace)
         (blkd : Pool) (cntr : nat) (heap : Heap) : Exn + Heap :=
  match fuel with
  | O => inl OutOfFuel
  | S fuel' =>
    match threads with
    | nil => if M.is_empty blkd then ret heap else inl (Deadlock blkd)
    | cons thd threads =>
      match randoms with
      | Cons rnd rs =>
        let (trc, others) := yank rnd thd threads in
        t <- (step trc others blkd cntr heap) ;;
        let '(thrds', blkd', cntr', heap') := t in
        sched fuel' rs thrds' blkd' cntr' heap'
      end
    end
  end.

Definition runPar (randoms : Stream nat) (p : Par Val) : Exn + Val :=
  let initHeap := singleton 0 None in
  let initThreads := [ runCont p (fun v => Put 0 v Done) ] in
  let maxFuel := 100 in
  finalHeap <- sched maxFuel randoms initThreads (M.empty _) 1 initHeap ;;
  match joinM (HM.find 0 finalHeap) with
  | None => inl HeapExn
  | Some finalVal => ret finalVal
  end
.

CoFixpoint iterate {A} (f : A -> A) (a : A) : Stream A :=
  Cons a (iterate f (f a)).

Definition canonical : Stream nat := const 0.
Definition round_robin : Stream nat := iterate S O.

Example err : Par Val :=
  v <- new ;;
  put v 3 ;;
  put v 4 ;;
  get v
.

Example deadlock : Par Val :=
  v <- new ;;
  get v
.

Eval cbn in runPar round_robin err.
Eval cbn in runPar round_robin deadlock.

Example dag1 : Par Val :=
  a <- new ;;
  b <- new ;;
  fork (x <- get a ;; put b x) ;;
  put a 100 ;;
  get b
.

Eval cbn in runPar canonical dag1.
Eval cbn in runPar round_robin dag1.

Example heap1 : Heap := singleton 0 None.
Example heap2 : Heap := singleton 0 (Some 1).

Eval cbv in H.lt heap1 heap2.

(* Fixpoint loopit {A} (acc : Val) (vr : IVar Val) : Par A := *)
(*   bind (get vr) (fun n => loopit (acc + n) vr). *)
