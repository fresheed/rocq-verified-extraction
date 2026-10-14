From Malfunction.Examples.oxcaml Require Import test_backend.
Import ListNotations MonadNotation.
Open Scope bs_scope.

Module Left.
Definition external (x : nat) := S x.
End Left.
Module Right.
Definition external (x : nat) := x + 2.
End Right.
Definition with_quote' := 3.
Definition names := Nat.eqb (Left.external with_quote') 4 &&
                    Nat.eqb (Right.external with_quote') 5.
MetaRocq Run (emit_test "names" names).
