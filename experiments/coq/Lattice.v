Require Import Coq.Arith.PeanoNat.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.omega.Omega.

Generalizable All Variables.

Class PartialOrder (A : Type) := {
  ord : relation A;

  reflexive :> Reflexive ord;
  antisymmetric : forall {x y}, ord x y -> ord y x -> x = y;
  transitive :> Transitive ord
}.

Infix "≤" := ord (at level 50).

Reserved Infix "⊔" (at level 36, left associativity).
Reserved Infix "⊓" (at level 40, left associativity).

Class JoinSemiLattice {A : Type} `(@PartialOrder A) := {
  join : A -> A -> A where "x ⊔ y" := (join x y);

  join_commutative : forall a b, a ⊔ b = b ⊔ a;
  join_associative : forall a b c, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c);
  join_idempotent  : forall a, a ⊔ a = a;
  join_consistent : forall a b, a ≤ b <-> b = a ⊔ b
}.

Class MeetSemiLattice {A : Type} `(@PartialOrder A) := {
  meet : A -> A -> A where "x ⊓ y" := (meet x y);

  meet_commutative : forall a b, a ⊓ b = b ⊓ a;
  meet_associative : forall a b c, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c);
  meet_idempotent  : forall a, a ⊓ a = a;
  meet_consistent : forall a b, a ≤ b <-> a = a ⊓ b
}.

Infix "⊔" := join (at level 36, left associativity).
Infix "⊓" := meet (at level 40, left associativity).

Class Lattice {A : Type} `{P : @PartialOrder A} `(@JoinSemiLattice A P) `(@MeetSemiLattice A P) := {
  meet_absorptive  : forall a b, a ⊓ (a ⊔ b) = a;
  join_absorptive  : forall a b, a ⊔ (a ⊓ b) = a
}.

Reserved Notation "⊤".
Reserved Notation "⊥".

Class BoundedLattice {A : Type} `{P : @PartialOrder A} `(@JoinSemiLattice A P) `(@MeetSemiLattice A P) := {
  top : A where "⊤" := top;
  bot : A where "⊥" := bot;

  top_identity : forall a, a ⊓ ⊤ = a;
  bot_identity : forall a, a ⊔ ⊥ = a
}.

Instance nat_PartialOrder : PartialOrder nat := {
  ord m n := m <= n
}.

Proof.
  - auto.
  - intros. omega.
  - unfold Transitive. intros. omega.
Qed.

Instance nat_MeetSemiLattice : MeetSemiLattice nat_PartialOrder := {
  meet m n := min m n
}.

Proof.
Admitted.

Instance nat_JoinSemiLattice : JoinSemiLattice nat_PartialOrder := {
  join m n := max m n
}.

Proof.
Admitted.
