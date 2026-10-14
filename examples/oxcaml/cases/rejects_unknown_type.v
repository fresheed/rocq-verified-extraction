From Malfunction.Examples.oxcaml Require Import test_backend.
Import ListNotations MonadNotation.
Open Scope bs_scope.

Example rejects_unknown_type :
  expect_error (OxcamlBackend.print_type 10 [] [] ExAst.TAny) = true.
Proof. vm_compute. reflexivity. Qed.
