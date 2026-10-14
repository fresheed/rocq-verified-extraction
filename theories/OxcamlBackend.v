(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import List Bool Arith.
From MetaRocq.Utils Require Import utils bytestring.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EAst.
From MetaRocq.Erasure.Typed Require Import ExAst.

Import ListNotations.
Open Scope bs_scope.

(** A native OCaml emitter for the typed erased AST, before deargumentation
    and constructors-as-blocks. Inspired by the separation of types, expressions
    and declarations in Rocq's extraction backend; no MiniML translation is used.

    This is an executable printer, NOT a verified OCaml extraction theorem.
    In particular, we do not implement MiniML's type reconstruction/Obj.magic
    insertion. Unknown types and unsupported runtime features are errors.
    The OCaml compiler remains the final check of target typability, including
    OCaml's value restriction and restrictions on polymorphic recursion.

    [emit_ocaml (env, term)] returns [Ok source] or [Error diagnostic].
    The source defines native algebraic types, annotated top-level values and
    [extracted_main]. Names carry environment indices, so they are unique but
    not a stable external API. [TBox] becomes [unit]; constructor parameters
    are accepted by curried wrappers and omitted from constructor fields.
    Axioms, primitive values, coinduction, lazy/force, constructor blocks and
    higher-kinded/unknown types require additional backend support.

    For a quoted Template program, use [compile_oxcaml] in OxcamlPipeline.
    End-to-end tests: [python3 examples/oxcaml/test_backend.py]. *)
Module OxcamlBackend.

Inductive result (A : Type) :=
| Ok : A -> result A
| Error : bytestring.string -> result A.
Arguments Ok {A} _.
Arguments Error {A} _.

Definition bind {A B} (r : result A) (f : A -> result B) : result B :=
  match r with Ok x => f x | Error e => Error e end.
Notation "x <- r ;; k" := (bind r (fun x => k))
  (at level 100, r at next level, right associativity).

Fixpoint traverse {A B} (f : A -> result B) (xs : list A) : result (list B) :=
  match xs with
  | [] => Ok []
  | x :: xs => y <- f x ;; ys <- traverse f xs ;; Ok (y :: ys)
  end.

Fixpoint join (sep : bytestring.string) (xs : list bytestring.string) :=
  match xs with [] => "" | [x] => x | x :: xs => x ++ sep ++ join sep xs end.
Definition parens s := "(" ++ s ++ ")".
Definition number := string_of_nat.
Definition nl : bytestring.string := String.String "010"%byte String.EmptyString.

(** Escape underscores as well as punctuation, so escaping is injective.
    Prefixes separate OCaml's value, type, constructor and local namespaces.
    Environment positions disambiguate globals even with equal printed paths. *)
Definition encode_byte (b : Byte.byte) : bytestring.string :=
  let n := Byte.to_nat b in
  if ((48 <=? n) && (n <=? 57)) ||
     ((65 <=? n) && (n <=? 90)) || ((97 <=? n) && (n <=? 122))
  then String.String b String.EmptyString
  else "_" ++ number n ++ "_".
Fixpoint encode (s : bytestring.string) :=
  match s with
  | String.EmptyString => ""
  | String.String b s => encode_byte b ++ encode s
  end.
Fixpoint global_index (Σ : ExAst.global_env) (kn : kername) : option nat :=
  match Σ with
  | [] => None
  | (kn', _, _) :: tl =>
    if eq_kername kn kn' then Some 0 else option_map S (global_index tl kn)
  end.
Definition global_name Σ kn : result bytestring.string :=
  match global_index Σ kn with
  | Some n => Ok (number n ++ "_" ++ encode kn.2)
  | None => Error ("Missing global: " ++ string_of_kername kn)
  end.
Definition value_name Σ kn := n <- global_name Σ kn ;; Ok ("v_" ++ n).
Definition type_name Σ ind :=
  n <- global_name Σ ind.(inductive_mind) ;;
  Ok ("t_" ++ n ++ "_" ++ number ind.(inductive_ind)).
Definition alias_name Σ kn := n <- global_name Σ kn ;; Ok ("t_" ++ n).
Definition constructor_name Σ ind c :=
  n <- global_name Σ ind.(inductive_mind) ;;
  match ExAst.lookup_constructor Σ ind c with
  | Some (id, _, _) =>
      Ok ("C_" ++ n ++ "_" ++ number ind.(inductive_ind) ++ "_" ++
          number c ++ "_" ++ encode id)
  | None => Error "Missing constructor"
  end.
Definition locals start count := map (fun i => "x" ++ number i) (seq start count).
Definition type_var n := "'a" ++ number n.
Definition keep_type_var (v : ExAst.type_var_info) :=
  v.(ExAst.tvar_is_arity) && negb v.(ExAst.tvar_is_logical).
Definition type_parameters vs :=
  map (fun iv => type_var iv.1)
      (filter (fun iv => keep_type_var iv.2) (combine (seq 0 (length vs)) vs)).
Definition parameters vs :=
  match vs with [] => "" | [v] => v ++ " " | _ => parens (join ", " vs) ++ " " end.

Fixpoint type_spine (t : ExAst.box_type) : ExAst.box_type * list ExAst.box_type :=
  match t with
  | ExAst.TApp f a => let '(h, args) := type_spine f in (h, (args ++ [a])%list)
  | _ => (t, [])
  end.
Fixpoint select_type_args (vs : list ExAst.type_var_info) (args : list ExAst.box_type)
  : result (list ExAst.box_type) :=
  match vs, args with
  | [], [] => Ok []
  | v :: vs, a :: args =>
    rest <- select_type_args vs args ;;
    Ok (if keep_type_var v then a :: rest else rest)
  | _, _ => Error "Type application arity mismatch"
  end.

Fixpoint print_type (fuel : nat) (Σ : ExAst.global_env) (vars : list bytestring.string)
  (t : ExAst.box_type) : result bytestring.string :=
  match fuel with
  | 0 => Error "Type printing depth limit exceeded"
  | S fuel =>
    match t with
    | ExAst.TBox => Ok "unit"
    | ExAst.TAny => Error "Unknown erased type: native OCaml needs type reconstruction"
    | ExAst.TVar n =>
      if existsb (eqb (type_var n)) vars then Ok (type_var n)
      else Error "Unbound erased type variable"
    | ExAst.TArr a b =>
      a <- print_type fuel Σ vars a ;; b <- print_type fuel Σ vars b ;;
      Ok (parens (a ++ " -> " ++ b))
    | _ =>
      let '(h, args) := type_spine t in
      match h with
      | ExAst.TInd ind =>
        match ExAst.lookup_inductive Σ ind with
        | None => Error "Missing inductive type"
        | Some body =>
          if body.(ExAst.ind_propositional) then Ok "unit" else
          args <- select_type_args body.(ExAst.ind_type_vars) args ;;
          args <- traverse (print_type fuel Σ vars) args ;;
          n <- type_name Σ ind ;; Ok (parens (parameters args ++ n))
        end
      | ExAst.TConst kn =>
        match ExAst.lookup_env Σ kn with
        | Some (ExAst.TypeAliasDecl (Some (vs, _))) =>
          args <- select_type_args vs args ;;
          args <- traverse (print_type fuel Σ vars) args ;;
          n <- alias_name Σ kn ;; Ok (parens (parameters args ++ n))
        | _ => Error "Missing or abstract type alias"
        end
      | _ => Error "Higher-kinded type application is not supported by native OCaml"
      end
    end
  end.

Definition constructor_pattern n xs :=
  match xs with [] => n | _ => n ++ " " ++ parens (join ", " xs) end.

Fixpoint print_term (fuel : nat) (Σ : ExAst.global_env)
  (ctx : list bytestring.string) (t : EAst.term) : result bytestring.string :=
  match fuel with
  | 0 => Error "Term printing depth limit exceeded"
  | S fuel =>
    let recur := print_term fuel Σ in
    match t with
    | EAst.tBox => Ok "()"
    | EAst.tRel n =>
      match nth_error ctx n with
      | Some x => Ok x | None => Error "Unbound de Bruijn index"
      end
    | EAst.tVar _ => Error "Free variables are not supported"
    | EAst.tEvar _ _ => Error "Unresolved evar"
    | EAst.tLambda _ body =>
      let x := "x" ++ number (length ctx) in
      body <- recur (x :: ctx) body ;;
      Ok (parens ("fun " ++ x ++ " -> " ++ body))
    | EAst.tLetIn _ value body =>
      let x := "x" ++ number (length ctx) in
      value <- recur ctx value ;; body <- recur (x :: ctx) body ;;
      Ok (parens ("let " ++ x ++ " = " ++ value ++ " in " ++ body))
    | EAst.tApp f a =>
      f <- recur ctx f ;; a <- recur ctx a ;; Ok (parens (f ++ " " ++ a))
    | EAst.tConst kn =>
      match ExAst.lookup_env Σ kn with
      | Some (ExAst.ConstantDecl _) => value_name Σ kn
      | Some (ExAst.TypeAliasDecl _) => Ok "()"
      | _ => Error "Missing constant"
      end
    | EAst.tConstruct ind c args =>
      match args with
      | _ :: _ => Error "Constructor blocks are not supported; use the pre-block pipeline"
      | [] =>
        match ExAst.lookup_constructor_full Σ ind c with
        | None => Error "Missing constructor"
        | Some (mib, oib, (_, _, arity)) =>
          if oib.(ExAst.ind_propositional) then Error "Unexpected propositional constructor" else
          n <- constructor_name Σ ind c ;;
          let xs := locals (length ctx) (mib.(ExAst.ind_npars) + arity) in
          let body := constructor_pattern n (skipn mib.(ExAst.ind_npars) xs) in
          Ok (match xs with
              | [] => body
              | _ => parens ("fun " ++ join " " xs ++ " -> " ++ body)
              end)
        end
      end
    | EAst.tCase (ind, npars) scrut branches =>
      match ExAst.lookup_minductive Σ ind.(inductive_mind), ExAst.lookup_inductive Σ ind with
      | Some mib, Some oib =>
        if negb (Nat.eqb npars mib.(ExAst.ind_npars)) then Error "Case parameter mismatch" else
        if negb (Nat.eqb (length branches) (length oib.(ExAst.ind_ctors)))
        then Error "Case branch count mismatch" else
        scrut <- recur ctx scrut ;;
        bs <- traverse (fun '(i, (nas, body)) =>
          match nth_error oib.(ExAst.ind_ctors) i with
          | None => Error "Missing branch constructor"
          | Some (_, _, arity) =>
            if negb (Nat.eqb (length nas) arity) then Error "Branch binder count mismatch" else
            n <- constructor_name Σ ind i ;;
            let xs := locals (length ctx) arity in
            body <- recur (rev xs ++ ctx)%list body ;;
            Ok ("| " ++ constructor_pattern n xs ++ " -> " ++ body)
          end) (combine (seq 0 (length branches)) branches) ;;
        match bs with
        | [] => Error "Empty elimination needs a target type annotation"
        | _ => Ok (parens ("match " ++ scrut ++ " with" ++ nl ++ join nl bs))
        end
      | _, _ => Error "Missing case inductive"
      end
    | EAst.tProj p scrut =>
      match ExAst.lookup_constructor_full Σ p.(proj_ind) 0 with
      | Some (mib, oib, (_, _, arity)) =>
        if negb (Nat.eqb (length oib.(ExAst.ind_ctors)) 1 &&
                 Nat.eqb p.(proj_npars) mib.(ExAst.ind_npars))
        then Error "Invalid record projection" else
        let xs := locals (length ctx) arity in
        match nth_error xs p.(proj_arg) with
        | None => Error "Projection index out of bounds"
        | Some x =>
          n <- constructor_name Σ p.(proj_ind) 0 ;; scrut <- recur ctx scrut ;;
          Ok (parens ("match " ++ scrut ++ " with " ++ constructor_pattern n xs ++ " -> " ++ x))
        end
      | _ => Error "Missing projection constructor"
      end
    | EAst.tFix defs idx =>
      let names := locals (length ctx) (length defs) in
      match nth_error names idx with
      | None => Error "Fixpoint index out of bounds"
      | Some selected =>
        ds <- traverse (fun '(n, d) =>
          match d.(EAst.dbody) with
          | EAst.tLambda _ _ =>
            body <- recur (rev names ++ ctx)%list d.(EAst.dbody) ;;
            Ok (n ++ " = " ++ body)
          | _ => Error "OCaml recursive definitions must be functions"
          end) (combine names defs) ;;
        Ok (parens ("let rec " ++ join (nl ++ "and ") ds ++ " in " ++ selected))
      end
    | EAst.tCoFix _ _ => Error "CoFix requires a coinductive runtime translation"
    | EAst.tPrim _ => Error "Primitive values require an OCaml runtime mapping"
    | EAst.tLazy _ | EAst.tForce _ => Error "Lazy/force requires a typed runtime translation"
    end
  end.

Definition print_inductive fuel Σ kn (mib : ExAst.mutual_inductive_body)
  (i : nat) (oib : ExAst.one_inductive_body) : result bytestring.string :=
  let ind := mkInd kn i in
  let vars := type_parameters oib.(ExAst.ind_type_vars) in
  n <- type_name Σ ind ;;
  cs <- traverse (fun '(c, (_, args, arity)) =>
    if negb (Nat.eqb (length args) (mib.(ExAst.ind_npars) + arity))
    then Error "Constructor type/term arity mismatch (deargumented input?)" else
    args <- traverse (fun a => print_type fuel Σ vars a.2)
                     (skipn mib.(ExAst.ind_npars) args) ;;
    n <- constructor_name Σ ind c ;;
    Ok ("| " ++ n ++ match args with [] => "" | _ => " of " ++ join " * " args end))
    (combine (seq 0 (length oib.(ExAst.ind_ctors))) oib.(ExAst.ind_ctors)) ;;
  Ok (parameters vars ++ n ++ " =" ++ nl ++
      match cs with [] => "|" | _ => join nl cs end).

Definition print_decl fuel Σ (entry : kername * bool * ExAst.global_decl)
  : result bytestring.string :=
  let '(kn, _, decl) := entry in
  match decl with
  | ExAst.ConstantDecl c =>
    match c.(ExAst.cst_body) with
    | None => Error ("Axiom needs an OCaml implementation: " ++ string_of_kername kn)
    | Some body =>
      n <- value_name Σ kn ;;
      ty <- print_type fuel Σ (map type_var (seq 0 (length c.(ExAst.cst_type).1))) c.(ExAst.cst_type).2 ;;
      body <- print_term fuel Σ [] body ;;
      Ok ("let " ++ n ++ " : " ++ ty ++ " = " ++ body ++ nl)
    end
  | ExAst.InductiveDecl mib =>
    match mib.(ExAst.ind_finite) with
    | CoFinite => Error "Coinductive declarations require a runtime translation"
    | _ =>
      let bodies := filter (fun ib => negb ib.2.(ExAst.ind_propositional))
        (combine (seq 0 (length mib.(ExAst.ind_bodies))) mib.(ExAst.ind_bodies)) in
      ds <- traverse (fun '(i, b) => print_inductive fuel Σ kn mib i b) bodies ;;
      Ok (match ds with [] => "" | _ => "type " ++ join (nl ++ "and ") ds ++ nl end)
    end
  | ExAst.TypeAliasDecl None => Error ("Abstract type alias: " ++ string_of_kername kn)
  | ExAst.TypeAliasDecl (Some (vs, ty)) =>
    let vars := type_parameters vs in
    n <- alias_name Σ kn ;; ty <- print_type fuel Σ vars ty ;;
    Ok ("type " ++ parameters vars ++ n ++ " = " ++ ty ++ nl)
  end.

Definition emit_ocaml_with_fuel fuel (p : ExAst.global_env * EAst.term)
  : result bytestring.string :=
  ds <- traverse (fun entry =>
    match print_decl fuel p.1 entry with
    | Ok s => Ok s
    | Error e => Error (string_of_kername entry.1.1 ++ ": " ++ e)
    end) (rev p.1) ;;
  main <- print_term fuel p.1 [] p.2 ;;
  Ok ("(* Generated from MetaRocq typed erasure. *)" ++ nl ++
      join nl ds ++ nl ++ "let extracted_main = " ++ main ++ nl).

(** [fuel] bounds AST nesting, not the number of declarations. *)
Definition emit_ocaml := emit_ocaml_with_fuel 4096.

End OxcamlBackend.
