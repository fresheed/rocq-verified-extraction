From Malfunction.Examples.oxcaml Require Import test_backend.
Import ListNotations MonadNotation.
Open Scope bs_scope.

Module Left.
Definition external (x : nat) := S x.
Inductive token := Token.
Definition read_token (x : token) := match x with Token => 1 end.
End Left.
Module Right.
Definition external (x : nat) := x + 2.
Inductive token := Token.
Definition read_token (x : token) := match x with Token => 2 end.
End Right.
(* These names compete with suffixes, keywords and case-normalized names. *)
Inductive token_1 := Token_1.
Definition external__1 := 3.
Definition Mixed := 4.
Definition mixed := 5.
Definition x := 6.
Definition capture_check (x : nat) := x + names.x.
Definition with_quote' := 3.
Definition names := Nat.eqb (Left.external with_quote') 4 &&
                    Nat.eqb (Right.external with_quote') 5 &&
                    Nat.eqb (Left.read_token Left.Token) 1 &&
                    Nat.eqb (Right.read_token Right.Token) 2 &&
                    (match Token_1 with Token_1 => true end) &&
                    Nat.eqb external__1 3 && Nat.eqb Mixed 4 &&
                    Nat.eqb mixed 5 && Nat.eqb (capture_check 1) 7.
MetaRocq Run (emit_test names).
