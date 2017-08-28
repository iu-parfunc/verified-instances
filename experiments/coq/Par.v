Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.
Require Import Coq.Program.Basics.

Require Import Trace.

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
