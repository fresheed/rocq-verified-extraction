From Malfunction.Examples.oxcaml Require Import test_backend.
Import ListNotations MonadNotation.
Open Scope bs_scope.

Inductive empty : Type := .
Definition empty_identity (x : empty) := x.
MetaRocq Run (emit_test "empty_type" empty_identity).
