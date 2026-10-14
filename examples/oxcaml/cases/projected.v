From Malfunction.Examples.oxcaml Require Import test_backend.
Import ListNotations MonadNotation.
Open Scope bs_scope.

Set Primitive Projections.
Record pair := { first : nat; second : nat }.
Definition projected :=
  let p := {| first := 2; second := 5 |} in
  Nat.eqb (first p) 2 && Nat.eqb (second p) 5.
MetaRocq Run (emit_test "projected" projected).
