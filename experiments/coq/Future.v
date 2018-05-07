Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Open Scope type_scope.

Definition Exn : Set := string.

Inductive Future (A : Type) : Type :=
  mkFuture : Exn + A -> Future A.

Arguments mkFuture {_} _.

Definition runFuture {A} (fa : Future A) : Exn + A :=
  match fa with
    mkFuture ea => ea
  end.

Definition retFuture {A} (a : A) : Future A :=
  mkFuture (inr a).

Definition mapFuture {A B} (fa : Future A) (f : A -> B) : Future B :=
  match fa with
  | mkFuture (inl e) => mkFuture (inl e)
  | mkFuture (inr a) => mkFuture (inr (f a))
  end.

Definition bindFuture {A B} (fa : Future A) (f : A -> Future B) : Future B :=
  match fa with
  | mkFuture (inl e) => mkFuture (inl e)
  | mkFuture (inr a) => f a
  end.

Opaque runFuture retFuture mapFuture bindFuture.
