Ltac destructo :=
  repeat
    match goal with
    | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
      match type of X with
      | option _ => destruct X
      end
    | [ |- context [ match ?X with _ => _ end ] ] =>
      match type of X with
      | option _ => destruct X
      end
    end.

Ltac destruct_if :=
  repeat
    match goal with
    | [ H : context [ if ?X then _ else _ ] |- _ ] => destruct X
    | [ |- context [ if ?X then _ else _ ] ] => destruct X
    end.

Ltac invert H :=
  inversion H; subst; clear H.

Ltac invert_inlr :=
  repeat
    match goal with
    | [ H : inl _ = inl _ |- _ ] => invert H
    | [ H : inl _ = inr _ |- _ ] => invert H
    | [ H : inr _ = inl _ |- _ ] => invert H
    | [ H : inr _ = inr _ |- _ ] => invert H
    end.
