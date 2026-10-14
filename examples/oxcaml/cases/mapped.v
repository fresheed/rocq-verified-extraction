From Malfunction.Examples.oxcaml Require Import test_backend.
Import ListNotations MonadNotation.
Open Scope bs_scope.

Definition mapped :=
  match List.map (fun n => n + 2) [1; 2; 3] with
  | [a; b; c] => Nat.eqb a 3 && Nat.eqb b 4 && Nat.eqb c 5
  | _ => false
  end.
MetaRocq Run (emit_test "mapped" mapped).
