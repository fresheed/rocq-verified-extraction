From Malfunction.Examples.oxcaml Require Import test_backend.
Import ListNotations MonadNotation.
Open Scope bs_scope.

From Stdlib Require Import Arith Lia List.

Section Floyd.

Variable A : Type.
Variable eq_dec : forall a b : A, {a = b} + {a <> b}.
Variable next : A -> option A.
Variable x0 : A.

(* ---------------------------------------------------------------- *)
(*  Positions in the list                                           *)
(* ---------------------------------------------------------------- *)

(* One pointer step, lifted to option (null stays null). *)
Definition step (o : option A) : option A :=
  match o with
  | Some a => next a
  | None => None
  end.

Fixpoint itr (n : nat) (o : option A) : option A :=
  match n with
  | 0 => o
  | S n => step (itr n o)
  end.

(* pos n = the node reached after following n pointers from x0. *)
Definition pos (n : nat) : option A := itr n (Some x0).

Lemma pos_0 : pos 0 = Some x0.
Proof. reflexivity. Qed.

Lemma pos_S : forall n, pos (S n) = step (pos n).
Proof. reflexivity. Qed.

Lemma itr_add : forall m n o, itr (m + n) o = itr m (itr n o).
Proof. induction m; intros; simpl; [reflexivity | now rewrite IHm]. Qed.

Lemma pos_add : forall m n, pos (m + n) = itr m (pos n).
Proof. intros. apply itr_add. Qed.

Lemma itr_None : forall m, itr m None = None.
Proof. induction m; simpl; [reflexivity | now rewrite IHm]. Qed.

(* ---------------------------------------------------------------- *)
(*  Specification                                                   *)
(* ---------------------------------------------------------------- *)

(* The list has a cycle: some live node is revisited after k > 0 steps. *)
Definition has_cycle : Prop :=
  exists i k, 0 < k /\ pos i <> None /\ pos (i + k) = pos i.

(* Once null is reached it is never left. *)
Lemma pos_None_mono : forall n m, pos n = None -> n <= m -> pos m = None.
Proof.
  intros n m Hn Hle.
  replace m with ((m - n) + n) by lia.
  rewrite pos_add, Hn. apply itr_None.
Qed.

(* After the cycle entry, the sequence is k-periodic. *)
Lemma periodic : forall i k, pos (i + k) = pos i ->
  forall j, i <= j -> pos (j + k) = pos j.
Proof.
  intros i k Hik j Hj.
  replace (j + k) with ((j - i) + (i + k)) by lia.
  replace j with ((j - i) + i) at 2 by lia.
  rewrite (pos_add (j - i) (i + k)), (pos_add (j - i) i), Hik.
  reflexivity.
Qed.

Lemma periodic_mult : forall i k, pos (i + k) = pos i ->
  forall q j, i <= j -> pos (j + q * k) = pos j.
Proof.
  intros i k Hik q. induction q as [|q IH]; intros j Hj.
  - now rewrite Nat.add_0_r.
  - replace (j + S q * k) with ((j + q * k) + k) by lia.
    rewrite (periodic i k Hik); [apply IH|]; lia.
Qed.

(* A null-terminated list has no cycle. *)
Lemma end_no_cycle : forall n, pos n = None -> ~ has_cycle.
Proof.
  intros n Hn (i & k & Hk & Hi & Hik).
  apply Hi.
  rewrite <- (periodic_mult i k Hik n i) by lia.
  apply (pos_None_mono n); [exact Hn | nia].
Qed.

(* ---------------------------------------------------------------- *)
(*  The algorithm                                                   *)
(* ---------------------------------------------------------------- *)

(* Tortoise s moves 1 step, hare f moves 2 steps per iteration.
   Some true  = cycle found, Some false = hit null, None = out of fuel.
   Fuel is only there because Rocq requires structural termination;
   floyd_terminates below says how much is enough. *)
Fixpoint floyd_loop (fuel : nat) (s f : A) : option bool :=
  match fuel with
  | 0 => None
  | S fuel =>
      match next f with
      | None => Some false
      | Some f1 =>
          match next f1 with
          | None => Some false
          | Some f2 =>
              match next s with
              | None => Some false
              | Some s1 =>
                  if eq_dec s1 f2 then Some true
                  else floyd_loop fuel s1 f2
              end
          end
      end
  end.

Definition floyd (fuel : nat) : option bool := floyd_loop fuel x0 x0.

(* ---------------------------------------------------------------- *)
(*  Soundness                                                       *)
(* ---------------------------------------------------------------- *)

(* Loop invariant: after t iterations, tortoise = pos t, hare = pos (2t). *)
Lemma loop_sound : forall fuel t s f b,
  pos t = Some s -> pos (2 * t) = Some f ->
  floyd_loop fuel s f = Some b -> (b = true <-> has_cycle).
Proof.
  induction fuel as [|fuel IH]; intros t s f b Hs Hf Hrun; [discriminate|].
  simpl in Hrun.
  assert (P1 : pos (2 * t + 1) = next f)
    by (rewrite Nat.add_1_r, pos_S, Hf; reflexivity).
  destruct (next f) as [f1|] eqn:E1.
  2:{ injection Hrun as <-. split; [discriminate|].
      intros H. exfalso. exact (end_no_cycle _ P1 H). }
  assert (P2 : pos (2 * t + 2) = next f1)
    by (replace (2 * t + 2) with (S (2 * t + 1)) by lia;
        rewrite pos_S, P1; reflexivity).
  destruct (next f1) as [f2|] eqn:E2.
  2:{ injection Hrun as <-. split; [discriminate|].
      intros H. exfalso. exact (end_no_cycle _ P2 H). }
  assert (P3 : pos (S t) = next s) by (rewrite pos_S, Hs; reflexivity).
  destruct (next s) as [s1|] eqn:E3.
  2:{ injection Hrun as <-. split; [discriminate|].
      intros H. exfalso. exact (end_no_cycle _ P3 H). }
  destruct (eq_dec s1 f2) as [<-|Hne].
  - (* tortoise and hare meet at index t+1 and 2(t+1) *)
    injection Hrun as <-. split; [intros _|reflexivity].
    exists (S t), (S t). repeat split.
    + lia.
    + rewrite P3. discriminate.
    + replace (S t + S t) with (2 * t + 2) by lia. now rewrite P2, P3.
  - apply (IH (S t) s1 f2); [exact P3 | | exact Hrun].
    replace (2 * S t) with (2 * t + 2) by lia. exact P2.
Qed.

Theorem floyd_sound : forall fuel b,
  floyd fuel = Some b -> (b = true <-> has_cycle).
Proof.
  intros fuel b H. apply (loop_sound fuel 0 x0 x0); auto.
Qed.

(* Unpacked forms. *)
Corollary floyd_true_cycle : forall fuel, floyd fuel = Some true -> has_cycle.
Proof. intros fuel H. now apply (floyd_sound fuel true H). Qed.

Corollary floyd_false_acyclic : forall fuel, floyd fuel = Some false -> ~ has_cycle.
Proof.
  intros fuel H Hc. apply (floyd_sound fuel false H) in Hc. discriminate.
Qed.

(* ---------------------------------------------------------------- *)
(*  Termination                                                     *)
(* ---------------------------------------------------------------- *)

(* The iteration leaving state t stops. *)
Definition stop (t : nat) : Prop :=
  pos (2 * t + 1) = None \/ pos (2 * t + 2) = None \/
  pos (S t) = None \/ pos (S t) = pos (2 * t + 2).

Lemma loop_terminates : forall d fuel t s f,
  pos t = Some s -> pos (2 * t) = Some f ->
  stop (d + t) -> d < fuel -> floyd_loop fuel s f <> None.
Proof.
  induction d as [|d IH]; intros fuel t s f Hs Hf Hstop Hfuel;
    (destruct fuel as [|fuel]; [lia|]); simpl.
  all: assert (P1 : pos (2 * t + 1) = next f)
         by (rewrite Nat.add_1_r, pos_S, Hf; reflexivity).
  all: destruct (next f) as [f1|] eqn:E1; [|discriminate].
  all: assert (P2 : pos (2 * t + 2) = next f1)
         by (replace (2 * t + 2) with (S (2 * t + 1)) by lia;
             rewrite pos_S, P1; reflexivity).
  all: destruct (next f1) as [f2|] eqn:E2; [|discriminate].
  all: assert (P3 : pos (S t) = next s) by (rewrite pos_S, Hs; reflexivity).
  all: destruct (next s) as [s1|] eqn:E3; [|discriminate].
  all: destruct (eq_dec s1 f2) as [_|Hne]; [discriminate|].
  - (* d = 0: the stop condition contradicts all branches being live *)
    unfold stop in Hstop. rewrite Nat.add_0_l in Hstop.
    rewrite P1, P2, P3 in Hstop.
    destruct Hstop as [H|[H|[H|H]]]; try discriminate.
    injection H as H. contradiction.
  - apply (IH fuel (S t) s1 f2); [exact P3 | | | lia].
    + replace (2 * S t) with (2 * t + 2) by lia. exact P2.
    + replace (d + S t) with (S d + t) by lia. exact Hstop.
Qed.

(* Fuel bounds: list length if null-terminated, mu + lambda if cyclic
   (where i, k are any witnesses, in particular the minimal ones). *)
Theorem floyd_terminates : forall fuel,
  (exists n, pos n = None /\ n <= fuel) \/
  (exists i k, 0 < k /\ pos i <> None /\ pos (i + k) = pos i /\ i + k <= fuel) ->
  floyd fuel <> None.
Proof.
  intros fuel [(n & Hn & Hle) | (i & k & Hk & Hi & Hik & Hle)].
  - destruct n as [|n]; [discriminate|].
    apply (loop_terminates n fuel 0 x0 x0); try reflexivity; [|lia].
    right; right; left. now rewrite Nat.add_0_r.
  - (* the meeting time: smallest multiple of k that is > i *)
    set (q := i / k + 1).
    set (t := q * k).
    assert (Hdm : i = k * (i / k) + i mod k) by (apply Nat.div_mod; lia).
    assert (Hmod : i mod k < k) by (apply Nat.mod_upper_bound; lia).
    assert (Ht1 : i < t) by (unfold t, q; nia).
    assert (Ht2 : t <= i + k) by (unfold t, q; nia).
    assert (Hmeet : pos (t + t) = pos t)
      by (apply (periodic_mult i k Hik q t); lia).
    apply (loop_terminates (t - 1) fuel 0 x0 x0); try reflexivity; [|lia].
    right; right; right.
    replace (S (t - 1 + 0)) with t by lia.
    replace (2 * (t - 1 + 0) + 2) with (t + t) by lia.
    now rewrite Hmeet.
Qed.

(* ---------------------------------------------------------------- *)
(*  Completeness for finite node types                              *)
(* ---------------------------------------------------------------- *)

(* Mapping a function that is injective on l preserves NoDup. *)
Lemma NoDup_map_inj {X Y} (g : X -> Y) (l : list X) :
  (forall a b, In a l -> In b l -> g a = g b -> a = b) ->
  NoDup l -> NoDup (map g l).
Proof.
  intros Hinj Hnd. induction Hnd as [|x l Hx Hnd IH]; simpl; constructor.
  - intros Hin. apply in_map_iff in Hin as (y & Hy & Hyl).
    assert (y = x) as -> by (apply Hinj; simpl; auto).
    contradiction.
  - apply IH. intros a b Ha Hb. apply Hinj; simpl; auto.
Qed.

(* If every node reachable from x0 lives in a list l, fuel = length l
   always suffices. Proof by pigeonhole. *)
Theorem floyd_complete_reachable : forall l : list A,
  (forall n a, pos n = Some a -> In a l) -> floyd (length l) <> None.
Proof.
  intros l Hfin Hnone.
  set (N := length l).
  (* By floyd_terminates, positions 0..N are all live ... *)
  assert (Hlive : forall n, n <= N -> pos n <> None).
  { intros n Hn Hp. apply (floyd_terminates N); [|exact Hnone].
    left. now exists n. }
  (* ... and pairwise distinct. *)
  assert (Hdist : forall i j, i < j <= N -> pos i <> pos j).
  { intros i j Hij Heq. apply (floyd_terminates N); [|exact Hnone].
    right. exists i, (j - i). repeat split; try lia.
    - apply Hlive. lia.
    - replace (i + (j - i)) with j by lia. now symmetry. }
  set (vals := map pos (seq 0 (S N))).
  assert (Hnd : NoDup vals).
  { apply NoDup_map_inj; [|apply seq_NoDup].
    intros a b Ha Hb Hab. apply in_seq in Ha, Hb.
    destruct (Nat.lt_trichotomy a b) as [Hlt|[Heq|Hgt]]; [|exact Heq|].
    - exfalso. apply (Hdist a b); [lia | exact Hab].
    - exfalso. apply (Hdist b a); [lia | now symmetry]. }
  assert (Hincl : incl vals (map Some l)).
  { intros v Hv. unfold vals in Hv. apply in_map_iff in Hv.
    destruct Hv as (n & <- & Hn). apply in_seq in Hn.
    destruct (pos n) as [a|] eqn:E.
    - apply in_map, (Hfin n), E.
    - exfalso. apply (Hlive n); [lia | exact E]. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
  unfold vals in Hlen. rewrite !length_map, length_seq in Hlen.
  fold N in Hlen. lia.
Qed.

Corollary floyd_complete_finite : forall l : list A,
  (forall a, In a l) -> floyd (length l) <> None.
Proof. intros l Hfin. apply floyd_complete_reachable. auto. Qed.

(* More fuel never changes an answer. *)
Lemma floyd_loop_mono : forall fuel fuel' s f b,
  floyd_loop fuel s f = Some b -> fuel <= fuel' -> floyd_loop fuel' s f = Some b.
Proof.
  induction fuel as [|fuel IH]; intros fuel' s f b H Hle; [discriminate|].
  destruct fuel' as [|fuel']; [lia|]. simpl in *.
  destruct (next f) as [f1|]; [|exact H].
  destruct (next f1) as [f2|]; [|exact H].
  destruct (next s) as [s1|]; [|exact H].
  destruct (eq_dec s1 f2); [exact H|]. apply (IH fuel'); [exact H | lia].
Qed.

(* Hence on a finite type Floyd is a decision procedure for has_cycle. *)
Corollary floyd_decides : forall l : list A, (forall a, In a l) ->
  exists b, floyd (length l) = Some b /\ (b = true <-> has_cycle).
Proof.
  intros l Hfin.
  destruct (floyd (length l)) as [b|] eqn:E.
  - exists b. split; [reflexivity | now apply (floyd_sound (length l))].
  - exfalso. exact (floyd_complete_finite l Hfin E).
Qed.

End Floyd.

(* ================================================================ *)
(*  Array interface                                                 *)
(* ================================================================ *)

(* The input is an array of nodes 0 .. length arr - 1, given as a list.
   arr[i] = Some j  means node i points to node j,
   arr[i] = None    means node i is the last node (null pointer).
   The list starts at node 0. A pointer to an index outside the array
   is treated as pointing to a node whose next is null. *)

Definition next_of (arr : list (option nat)) (i : nat) : option nat :=
  match nth_error arr i with
  | Some o => o
  | None => None
  end.

Definition arr_has_cycle (arr : list (option nat)) : Prop :=
  has_cycle nat (next_of arr) 0.

(* One more than the array length is always enough fuel. *)
Definition floyd_array (arr : list (option nat)) : bool :=
  match floyd nat Nat.eq_dec (next_of arr) 0 (S (length arr)) with
  | Some b => b
  | None => false   (* unreachable, see floyd_array_terminates *)
  end.

(* All pointer targets stored in the array. *)
Definition targets (arr : list (option nat)) : list nat :=
  flat_map (fun o => match o with Some j => [j] | None => [] end) arr.

Lemma targets_length : forall arr, length (targets arr) <= length arr.
Proof. induction arr as [|[j|] arr IH]; simpl; lia. Qed.

Lemma next_of_targets : forall arr i j, next_of arr i = Some j -> In j (targets arr).
Proof.
  intros arr i j H. unfold next_of in H.
  destruct (nth_error arr i) as [o|] eqn:E; [|discriminate]. subst o.
  apply in_flat_map. exists (Some j). split; [|now left].
  eapply nth_error_In; eauto.
Qed.

(* Every reachable node is 0 or a stored pointer target. *)
Lemma reachable_in : forall arr n a,
  pos nat (next_of arr) 0 n = Some a -> In a (0 :: targets arr).
Proof.
  intros arr [|n] a H.
  - injection H as <-. now left.
  - right. rewrite pos_S in H.
    destruct (pos nat (next_of arr) 0 n) as [b|]; [|discriminate].
    exact (next_of_targets arr b a H).
Qed.

Theorem floyd_array_terminates : forall arr,
  exists b, floyd nat Nat.eq_dec (next_of arr) 0 (S (length arr)) = Some b.
Proof.
  intros arr.
  pose proof (floyd_complete_reachable nat Nat.eq_dec (next_of arr) 0
                (0 :: targets arr) (reachable_in arr)) as H.
  destruct (floyd nat Nat.eq_dec (next_of arr) 0 (length (0 :: targets arr)))
    as [b|] eqn:E; [|contradiction].
  exists b. eapply floyd_loop_mono; [exact E|].
  simpl. pose proof (targets_length arr). lia.
Qed.

(* Main result: floyd_array decides whether the list has a cycle. *)
Theorem floyd_array_correct : forall (arr: list (option nat)),
  floyd_array arr = true <-> arr_has_cycle arr.
Proof.
  intros arr. unfold floyd_array, arr_has_cycle.
  destruct (floyd_array_terminates arr) as [b E]. rewrite E.
  exact (floyd_sound nat Nat.eq_dec (next_of arr) 0 _ b E).
Qed.

(* ---------------------------------------------------------------- *)
(*  Sanity checks                                                   *)
(* ---------------------------------------------------------------- *)

Definition test_cases: list (bool * bool) := [
  (* 0 -> 1 -> 2 -> 3 -> 4 -> 2   (rho-shaped) *)
  (floyd_array [Some 1; Some 2; Some 3; Some 4; Some 2], true);
  (* 0 -> 1 -> 2 -> 3 -> null *)
  (floyd_array [Some 1; Some 2; Some 3; None], false);
  (* 0 -> 0   (self-loop) *)
  (floyd_array [Some 0], true);
  (* 0 -> 2 -> null; node 1 is on a cycle 1 -> 1 but unreachable *)
  (floyd_array [Some 2; Some 1; None], false);
  (* 0 -> 7 (out of bounds, treated as null) *)
  (floyd_array [Some 7], false)
].

Definition tests_result := forallb (fun '(c, e) => eqb c e) test_cases.

Theorem tests_correct: tests_result = true.
Proof. reflexivity. Qed.

MetaRocq Run (emit_test "two_ptr" tests_result).