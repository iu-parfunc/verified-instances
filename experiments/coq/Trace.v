Require Export Val.
Require Export IVar.

Inductive Trace : Type :=
  Get  : IVar Val -> (Val -> Trace) -> Trace
| Put  : IVar Val -> Val -> Trace -> Trace
| New  : (IVar Val -> Trace) -> Trace
| Fork : Trace -> Trace -> Trace
| Done : Trace
.
