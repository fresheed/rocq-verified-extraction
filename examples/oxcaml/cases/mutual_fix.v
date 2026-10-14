From Malfunction.Examples.oxcaml Require Import test_backend.
Import ListNotations MonadNotation.
Open Scope bs_scope.

Fixpoint even (n : nat) : bool :=
  match n with 0 => true | S n => odd n end
with odd (n : nat) : bool :=
  match n with 0 => false | S n => even n end.
Definition mutual_fix := even 6 && negb (odd 6) && odd 5.
MetaRocq Run (emit_test "mutual_fix" mutual_fix).
