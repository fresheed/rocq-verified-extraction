From Malfunction.Examples.oxcaml Require Import test_backend.
Import ListNotations MonadNotation.
Open Scope bs_scope.

Definition polymorphic_id {A : Type} (x : A) := x.
Definition basic :=
  let x := 3 in
  let x := S x in
  Nat.eqb (polymorphic_id x) 4 && polymorphic_id true.
MetaRocq Run (emit_test "basic" basic).
