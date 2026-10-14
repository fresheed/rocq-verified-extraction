From Malfunction.Examples.oxcaml Require Import test_backend.
Import ListNotations MonadNotation.
Open Scope bs_scope.

Definition captured :=
  let f := fun x => let fix go n :=
    match n with 0 => x | S n => S (go n) end in go in
  Nat.eqb (f 4 3) 7.
MetaRocq Run (emit_test "captured" captured).
