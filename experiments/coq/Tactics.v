Ltac destruct_b :=
  repeat
    match goal with
    | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
      match type of X with
      | prod _ _ => destruct X eqn:?
      | sum  _ _ => destruct X eqn:?
      | option _ => destruct X eqn:?
      | list _   => destruct X eqn:?
      end
    | [ H : context [ let _ := ?X in _ ] |- _ ] =>
      match type of X with
      | prod _ _ => destruct X eqn:?
      | sum  _ _ => destruct X eqn:?
      | option _ => destruct X eqn:?
      | list _   => destruct X eqn:?
      end
    | [ |- context [ match ?X with _ => _ end ] ] =>
      match type of X with
      | prod _ _ => destruct X eqn:?
      | sum  _ _ => destruct X eqn:?
      | option _ => destruct X eqn:?
      | list   _ => destruct X eqn:?
      end
    | [ |- context [ let _ := ?X in _ ] ] =>
      match type of X with
      | prod _ _ => destruct X eqn:?
      | sum  _ _ => destruct X eqn:?
      | option _ => destruct X eqn:?
      | list   _ => destruct X eqn:?
      end
    end.

Ltac destruct_if :=
  repeat
    match goal with
    | [ H : context [ if ?X then _ else _ ] |- _ ] => destruct X
    | [ |- context [ if ?X then _ else _ ] ] => destruct X
    end.

Ltac destructo :=
  destruct_b; destruct_if; subst.

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

Ltac invert_opt :=
  repeat
    match goal with
    | [ H : None = Some _ |- _ ] => invert H
    | [ H : Some _ = None |- _ ] => invert H
    end.
