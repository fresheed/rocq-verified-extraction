From Malfunction.Examples.oxcaml Require Import test_backend.
Import ListNotations MonadNotation.
Open Scope bs_scope.

Example rejects_open_term :
  expect_error (OxcamlBackend.emit_ocaml ([], EAst.tRel 0)) = true.
Proof. vm_compute. reflexivity. Qed.
