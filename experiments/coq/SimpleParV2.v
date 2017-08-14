(** * SimplePar V2 *)

Set Asymmetric Patterns.

Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Monads.ListMonad.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Monads.EitherMonad.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Require Export Heap.
Require Export Trace.
Require Import Par.
Require Import Utils.

Inductive Exn : Type :=
  MultiplePut : Val -> nat -> Val -> Exn
| Deadlock : M.t (list (Val -> Trace)) -> Exn
| HeapExn : Exn
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

Fixpoint sched (randoms : list nat) (threads : list Trace)
         (blkd : Pool) (cntr : nat) (heap : Heap) : Exn + Heap :=
  match randoms, threads with
  | _ , nil => if M.is_empty blkd then ret heap else inl (Deadlock blkd)
  | nil , _ => if M.is_empty blkd then ret heap else inl (Deadlock blkd)
  | cons rnd rs, cons thd threads =>
    let (trc, others) := yank rnd thd threads in
    t <- (step trc others blkd cntr heap) ;;
      let '(thrds', blkd', cntr', heap') := t in
      sched rs thrds' blkd' cntr' heap'
  end.

Definition runPar (randoms : list nat) (p : Par Val) : Exn + Val :=
  let initHeap := singleton 0 None in
  let initThreads := [ runCont p (fun v => Put 0 v Done) ] in
  finalHeap <- sched randoms initThreads (M.empty _) 1 initHeap ;;
  match joinM (HM.find 0 finalHeap) with
  | None => inl HeapExn
  | Some finalVal => ret finalVal
  end
.

Fixpoint iterate {A} (f : A -> A) (a : A) (n : nat) : list A :=
  match n with
  | O => a :: []
  | S m => f a :: iterate f (f a) m
  end.

Definition canonical : list nat := repeat 0 42.
Definition round_robin : list nat := iterate S O 42.

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
