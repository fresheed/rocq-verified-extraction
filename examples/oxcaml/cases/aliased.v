From Malfunction.Examples.oxcaml Require Import test_backend.
Import ListNotations MonadNotation.
Open Scope bs_scope.

Definition nat_alias := nat.
Definition alias_id (x : nat_alias) : nat_alias := x.
Definition aliased := Nat.eqb (alias_id 3) 3.
MetaRocq Run (emit_test aliased).
