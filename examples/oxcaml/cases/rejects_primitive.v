From Malfunction.Examples.oxcaml Require Import test_backend.
Import ListNotations MonadNotation.
Open Scope bs_scope.

Example rejects_primitive :
  expect_error (OxcamlBackend.emit_ocaml
    ([], EAst.tPrim (EPrimitive.prim_int (Uint63.of_Z BinNums.Z0)))) = true.
Proof. vm_compute. reflexivity. Qed.
