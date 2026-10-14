From Malfunction.Examples.oxcaml Require Import test_backend.
Import ListNotations MonadNotation.
Open Scope bs_scope.

Example rejects_fuel_exhaustion :
  expect_error (OxcamlBackend.emit_ocaml_with_fuel 0 ([], EAst.tBox)) = true.
Proof. vm_compute. reflexivity. Qed.
