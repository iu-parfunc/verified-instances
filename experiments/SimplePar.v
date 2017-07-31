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

Hint Unfold joinM.

Module Import M := FMapList.Make(Nat_as_OT).

Definition add_with {A} (f : A -> A -> A) (key : nat) (new_val : A) (m : M.t A) : M.t A :=
  match find key m with
  | None => add key new_val m
  | Some old_val => add key (f new_val old_val) m
  end.

Definition singleton {A} (key : nat) (val : A) : M.t A :=
  M.add key val (M.empty A).

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

(** * SimplePar *)

Module SimplePar.

Definition Val := nat.

Definition IVar (A : Type) := nat.

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

Inductive Exn : Type :=
  MultiplePut : Val -> nat -> Val -> Exn
| Deadlock : M.t (list (Val -> Trace)) -> Exn
| HeapExn : Exn
| OutOfFuel : Exn
.

Definition Heap := M.t (option Val).

Definition Pool := M.t (list (Val -> Trace)).

Definition step (trc : Trace) (others : list Trace)
           (blkd : Pool) (cntr : nat) (heap : Heap)
  : Exn + (list Trace * Pool * nat * Heap) :=
  match trc with
  | Done => ret (others, blkd, cntr, heap)
  | Fork t1 t2 => ret (t1 :: t2 :: others, blkd, cntr, heap)
  | New k => ret (k cntr :: others, blkd, cntr + 1, M.add cntr None heap)
  | Get ix k => match joinM (M.find ix heap) with
               | None => ret (others, add_with (app (A:=_)) ix [k] blkd, cntr, heap)
               | Some v => ret (k v :: others, blkd, cntr, heap)
               end
  | Put ix v t2 => let heap' := M.add ix (Some v) heap in
                  match joinM (M.find ix heap) with
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
  match joinM (M.find 0 finalHeap) with
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

(* Fixpoint loopit {A} (acc : Val) (vr : IVar Val) : Par A := *)
(*   bind (get vr) (fun n => loopit (acc + n) vr). *)

End SimplePar.
