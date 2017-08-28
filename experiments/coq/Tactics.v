Ltac destruct_typ X :=
  match type of X with
  | prod _ _ => destruct X eqn:?
  | sum  _ _ => destruct X eqn:?
  | option _ => destruct X eqn:?
  | list _   => destruct X eqn:?
  | nat => destruct X eqn:?
  | comparison => destruct X eqn:?
  end.

Ltac destruct_match :=
  match goal with
  | [ H : context [ match ?X with _ => _ end ] |- _ ] => destruct_typ X
  | [ |- context [ match ?X with _ => _ end ] ] => destruct_typ X
  | [ H : context [ match ?X as _ return _ with _ => _ end ] |- _ ] => destruct_typ X
  | [ |- context [ match ?X as _ return _ with _ => _ end ] ] => destruct_typ X
  end.

Ltac destruct_let :=
  match goal with
  | [ H : context [ let _ := ?X in _ ] |- _ ] => destruct_typ X
  | [ |- context [ let _ := ?X in _ ] ] => destruct_typ X
  end.

Ltac destruct_if :=
  match goal with
  | [ H : context [ if ?X then _ else _ ] |- _ ] => destruct X
  | [ |- context [ if ?X then _ else _ ] ] => destruct X
  end.

Ltac destructo :=
  repeat (destruct_let || destruct_match || destruct_if); subst.

Ltac invert H :=
  inversion H; subst; clear H.

Ltac invert_sum :=
  match goal with
  | [ H : inl _ = inl _ |- _ ] => invert H
  | [ H : inl _ = inr _ |- _ ] => invert H
  | [ H : inr _ = inl _ |- _ ] => invert H
  | [ H : inr _ = inr _ |- _ ] => invert H
  end.

Ltac invert_option :=
  match goal with
  | [ H : None = Some _ |- _ ] => invert H
  | [ H : Some _ = None |- _ ] => invert H
  | [ H : Some _ = Some _ |- _ ] => invert H
  end.

Ltac inverto :=
  repeat (invert_sum || invert_option).
