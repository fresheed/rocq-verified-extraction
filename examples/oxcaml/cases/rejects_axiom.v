From Malfunction.Examples.oxcaml Require Import test_backend.
Import ListNotations MonadNotation.
Open Scope bs_scope.

Axiom external_axiom : nat.
MetaRocq Quote Recursively Definition quoted_axiom := external_axiom.
Example rejects_axiom : expect_error (compile_oxcaml quoted_axiom) = true.
Proof. vm_compute. reflexivity. Qed.
