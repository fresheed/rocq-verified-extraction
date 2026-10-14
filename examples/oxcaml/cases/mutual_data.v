From Malfunction.Examples.oxcaml Require Import test_backend.
Import ListNotations MonadNotation.
Open Scope bs_scope.

Inductive tree : Type := Node : forest -> tree
with forest : Type := Empty : forest | More : tree -> forest -> forest.
Fixpoint tree_size (t : tree) : nat :=
  match t with Node f => S (forest_size f) end
with forest_size (f : forest) : nat :=
  match f with Empty => 0 | More t f => tree_size t + forest_size f end.
Definition mutual_data := Nat.eqb (tree_size (Node (More (Node Empty) Empty))) 2.
MetaRocq Run (emit_test "mutual_data" mutual_data).
