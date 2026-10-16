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
    [extracted_main]. Names preserve source spelling where OCaml allows it; numeric suffixes
    are allocated only to resolve collisions. [TBox] becomes [unit]; constructor parameters
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

(** Keep legal OCaml spelling, including underscores and apostrophes. The
    allocator handles collisions caused by sanitization, case conversion and
    flattening Rocq modules into a single OCaml compilation unit. *)
Definition encode_byte (b : Byte.byte) : bytestring.string :=
  let n := Byte.to_nat b in
  if ((48 <=? n) && (n <=? 57)) ||
     ((65 <=? n) && (n <=? 90)) || ((97 <=? n) && (n <=? 122)) ||
     Nat.eqb n 95 || Nat.eqb n 39
  then String.String b String.EmptyString
  else "_" ++ number n ++ "_".
Fixpoint encode (s : bytestring.string) :=
  match s with
  | String.EmptyString => ""
  | String.String b s => encode_byte b ++ encode s
  end.
Definition keywords : list bytestring.string :=
  ["and"; "as"; "assert"; "asr"; "begin"; "class"; "constraint";
   "do"; "done"; "downto"; "else"; "end"; "exception"; "external";
   "false"; "for"; "fun"; "function"; "functor"; "if"; "in"; "include";
   "inherit"; "initializer"; "land"; "lazy"; "let"; "lor"; "lsl"; "lsr";
   "lxor"; "match"; "method"; "mod"; "module"; "mutable"; "new";
   "nonrec"; "object"; "of"; "open"; "or"; "private"; "rec"; "sig";
   "struct"; "then"; "to"; "true"; "try"; "type"; "val"; "virtual";
   "when"; "while"; "with"; "_"] .
Definition member (s : bytestring.string) (xs : list bytestring.string) := existsb (eqb s) xs.
Definition lower_initial (s : bytestring.string) :=
  match s with
  | String.EmptyString => "x"
  | String.String b tail =>
    let n := Byte.to_nat b in
    if (65 <=? n) && (n <=? 90)
    then String.String (match Byte.of_nat (n + 32) with Some b => b | None => b end) tail
    else if ((97 <=? n) && (n <=? 122)) || Nat.eqb n 95 then s
    else "x_" ++ s
  end.
Definition lower_name s :=
  let s := lower_initial (encode s) in
  if member s keywords then s ++ "_" else s.
Definition upper_name s :=
  let s := encode s in
  match s with
  | String.EmptyString => "C"
  | String.String b tail =>
    let n := Byte.to_nat b in
    if (97 <=? n) && (n <=? 122)
    then String.String (match Byte.of_nat (n - 32) with Some b => b | None => b end) tail
    else if (65 <=? n) && (n <=? 90) then s else "C_" ++ s
  end.

Inductive symbol :=
| ValueName (kn : kername)
| AliasName (kn : kername)
| InductiveName (ind : inductive)
| ConstructorName (ind : inductive) (c : nat).
Definition same_ind i j :=
  eq_kername i.(inductive_mind) j.(inductive_mind) &&
  Nat.eqb i.(inductive_ind) j.(inductive_ind).
Definition same_symbol a b :=
  match a, b with
  | ValueName a, ValueName b | AliasName a, AliasName b => eq_kername a b
  | InductiveName a, InductiveName b => same_ind a b
  | ConstructorName a i, ConstructorName b j => same_ind a b && Nat.eqb i j
  | _, _ => false
  end.
Definition namespace s :=
  match s with ValueName _ => 0 | ConstructorName _ _ => 1 | _ => 2 end.
Definition declaration_names (entry : kername * bool * ExAst.global_decl)
  : list (symbol * bytestring.string) :=
  let '(kn, _, decl) := entry in
  match decl with
  | ExAst.ConstantDecl _ => [(ValueName kn, lower_name kn.2)]
  | ExAst.TypeAliasDecl _ => [(AliasName kn, lower_name kn.2)]
  | ExAst.InductiveDecl mib =>
    flat_map (fun '(i, oib) =>
      let ind := mkInd kn i in
      (InductiveName ind, lower_name oib.(ExAst.ind_name)) ::
      map (fun '(c, (id, _, _)) => (ConstructorName ind c, upper_name id))
          (combine (seq 0 (length oib.(ExAst.ind_ctors))) oib.(ExAst.ind_ctors)))
      (combine (seq 0 (length mib.(ExAst.ind_bodies))) mib.(ExAst.ind_bodies))
  end.

Fixpoint fresh_suffix fuel n base used :=
  let candidate := base ++ "_" ++ number n in
  match fuel with
  | 0 => candidate
  | S fuel => if member candidate used then fresh_suffix fuel (S n) base used
              else candidate
  end.
Definition fresh_name base used :=
  if member base used then fresh_suffix (S (length used)) 1 base used else base.
Definition reserved ns : list bytestring.string :=
  match ns with
  | 0 => ["extracted_main"]
  | 2 => ["unit"] (* [TBox] uses OCaml's builtin unit, even if Rocq defines unit. *)
  | _ => []
  end.
Definition names_in ns (table : list (symbol * bytestring.string)) :=
  map snd (filter (fun entry => Nat.eqb ns (namespace entry.1)) table).
Fixpoint allocate_names (all pending used : list (symbol * bytestring.string)) :=
  match pending with
  | [] => used
  | (key, base) :: pending =>
    let ns := namespace key in
    let occupied := (reserved ns ++ names_in ns used)%list in
    (* Reserve other preferred spellings: disambiguating [foo] must not steal
       the spelling of a distinct source name [foo_1]. *)
    let name := if member base occupied
                then fresh_name base (occupied ++ names_in ns all)%list else base in
    allocate_names all pending ((key, name) :: used)
  end.
Definition name_table Σ :=
  let names := flat_map declaration_names (rev Σ) in allocate_names names names [].
Definition lookup_name table key : result bytestring.string :=
  match find (fun entry => same_symbol key entry.1) table with
  | Some (_, n) => Ok n
  | None => Error "Missing global name"
  end.
Definition value_name table kn := lookup_name table (ValueName kn).
Definition type_name table ind := lookup_name table (InductiveName ind).
Definition alias_name table kn := lookup_name table (AliasName kn).
Definition constructor_name table ind c := lookup_name table (ConstructorName ind c).
Definition local_name table ctx na :=
  let base := match na with nNamed s => lower_name s | nAnon => "x" end in
  fresh_name base (ctx ++ reserved 0 ++ names_in 0 table)%list.
Fixpoint local_names table ctx nas :=
  match nas with
  | [] => []
  | na :: nas => let n := local_name table ctx na in n :: local_names table (n :: ctx) nas
  end.

(** Strings are laid out relative to their first column. Each enclosing block
    indents every line of its child, rather than only adding leading spaces. *)
Fixpoint indent_tail (s : bytestring.string) : bytestring.string :=
  match s with
  | String.EmptyString => ""
  | String.String b s =>
    String.String b
      (if Nat.eqb (Byte.to_nat b) 10 then "  " ++ indent_tail s else indent_tail s)
  end.
Definition indent s := "  " ++ indent_tail s.
Definition at_precedence required (printed : nat * bytestring.string) :=
  if printed.1 <? required then parens printed.2 else printed.2.
Definition short s := (String.length s <=? 88) &&
  negb (existsb (fun b => Nat.eqb (Byte.to_nat b) 10) (String.print s)).
Definition application f args :=
  let flat := join " " (f :: args) in
  if short flat then flat else f ++ nl ++ indent (join nl args).

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

Fixpoint print_type_at (fuel : nat) (Σ : ExAst.global_env) (table : list (symbol * bytestring.string))
  (vars : list bytestring.string)
  (required : nat) (t : ExAst.box_type) : result bytestring.string :=
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
      a <- print_type_at fuel Σ table vars 2 a ;; b <- print_type_at fuel Σ table vars 1 b ;;
      Ok (at_precedence required (1, a ++ " -> " ++ b))
    | _ =>
      let '(h, args) := type_spine t in
      match h with
      | ExAst.TInd ind =>
        match ExAst.lookup_inductive Σ ind with
        | None => Error "Missing inductive type"
        | Some body =>
          if body.(ExAst.ind_propositional) then Ok "unit" else
          args <- select_type_args body.(ExAst.ind_type_vars) args ;;
          args <- traverse (print_type_at fuel Σ table vars 3) args ;;
          n <- type_name table ind ;; Ok (at_precedence required (match args with [] => 3 | _ => 2 end, parameters args ++ n))
        end
      | ExAst.TConst kn =>
        match ExAst.lookup_env Σ kn with
        | Some (ExAst.TypeAliasDecl (Some (vs, _))) =>
          args <- select_type_args vs args ;;
          args <- traverse (print_type_at fuel Σ table vars 3) args ;;
          n <- alias_name table kn ;; Ok (at_precedence required (match args with [] => 3 | _ => 2 end, parameters args ++ n))
        | _ => Error "Missing or abstract type alias"
        end
      | _ => Error "Higher-kinded type application is not supported by native OCaml"
      end
    end
  end.

Definition print_type fuel Σ vars := print_type_at fuel Σ (name_table Σ) vars 0.

Definition constructor_pattern n xs :=
  match xs with [] => n | _ => n ++ " " ++ parens (join ", " xs) end.

Fixpoint lambda_spine (t : EAst.term) : list name * EAst.term :=
  match t with
  | EAst.tLambda na body => let '(nas, body) := lambda_spine body in (na :: nas, body)
  | _ => ([], t)
  end.
Fixpoint term_spine (t : EAst.term) : EAst.term * list EAst.term :=
  match t with
  | EAst.tApp f a => let '(f, args) := term_spine f in (f, (args ++ [a])%list)
  | _ => (t, [])
  end.

(** Precedence: 0 = binding/match, 2 = application, 3 = atomic. *)
Fixpoint print_expr (fuel : nat) (Σ : ExAst.global_env)
  (table : list (symbol * bytestring.string))
  (ctx : list bytestring.string) (t : EAst.term) : result (nat * bytestring.string) :=
  match fuel with
  | 0 => Error "Term printing depth limit exceeded"
  | S fuel =>
    let recur := print_expr fuel Σ table in
    let render ctx prec t := p <- recur ctx t ;; Ok (at_precedence prec p) in
    match t with
    | EAst.tBox => Ok (3, "()")
    | EAst.tRel n =>
      match nth_error ctx n with
      | Some x => Ok (3, x) | None => Error "Unbound de Bruijn index"
      end
    | EAst.tVar _ => Error "Free variables are not supported"
    | EAst.tEvar _ _ => Error "Unresolved evar"
    | EAst.tLambda _ _ =>
      let '(nas, body) := lambda_spine t in
      let xs := local_names table ctx nas in
      body <- render (rev xs ++ ctx)%list 0 body ;;
      Ok (0, "fun " ++ join " " xs ++ " ->" ++ nl ++ indent body)
    | EAst.tLetIn na value body =>
      let x := local_name table ctx na in
      value <- render ctx 0 value ;; body <- render (x :: ctx) 0 body ;;
      Ok (0, "let " ++ x ++ " =" ++ nl ++ indent value ++ nl ++ "in" ++ nl ++ body)
    | EAst.tApp _ _ =>
      let '(f, args) := term_spine t in
      f <- render ctx 2 f ;; args <- traverse (render ctx 3) args ;;
      Ok (2, application f args)
    | EAst.tConst kn =>
      match ExAst.lookup_env Σ kn with
      | Some (ExAst.ConstantDecl _) => n <- value_name table kn ;; Ok (3, n)
      | Some (ExAst.TypeAliasDecl _) => Ok (3, "()")
      | _ => Error "Missing constant"
      end
    | EAst.tConstruct ind c args =>
      match args with
      | _ :: _ => Error "Constructor blocks are not supported; use the pre-block pipeline"
      | [] =>
        match ExAst.lookup_constructor_full Σ ind c with
        | None => Error "Missing constructor"
        | Some (mib, oib, (_, fields, arity)) =>
          if oib.(ExAst.ind_propositional) then Error "Unexpected propositional constructor" else
          n <- constructor_name table ind c ;;
          let xs := local_names table ctx (map fst fields) in
          if negb (Nat.eqb (length xs) (mib.(ExAst.ind_npars) + arity))
          then Error "Constructor type/term arity mismatch" else
          let body := constructor_pattern n (skipn mib.(ExAst.ind_npars) xs) in
          Ok (match xs with
              | [] => (3, body)
              | _ => (0, "fun " ++ join " " xs ++ " -> " ++ body)
              end)
        end
      end
    | EAst.tCase (ind, npars) scrut branches =>
      match ExAst.lookup_minductive Σ ind.(inductive_mind), ExAst.lookup_inductive Σ ind with
      | Some mib, Some oib =>
        if negb (Nat.eqb npars mib.(ExAst.ind_npars)) then Error "Case parameter mismatch" else
        if negb (Nat.eqb (length branches) (length oib.(ExAst.ind_ctors)))
        then Error "Case branch count mismatch" else
        scrut <- render ctx 1 scrut ;;
        bs <- traverse (fun '(i, (nas, body)) =>
          match nth_error oib.(ExAst.ind_ctors) i with
          | None => Error "Missing branch constructor"
          | Some (_, _, arity) =>
            if negb (Nat.eqb (length nas) arity) then Error "Branch binder count mismatch" else
            n <- constructor_name table ind i ;;
            (* Branch contexts are stored innermost first. *)
            let xs := local_names table ctx (rev nas) in
            body <- render (rev xs ++ ctx)%list 1 body ;;
            Ok ("| " ++ constructor_pattern n xs ++ " ->" ++ nl ++ indent body)
          end) (combine (seq 0 (length branches)) branches) ;;
        match bs with
        | [] => Error "Empty elimination needs a target type annotation"
        | _ => Ok (0, "match " ++ scrut ++ " with" ++ nl ++ join nl bs)
        end
      | _, _ => Error "Missing case inductive"
      end
    | EAst.tProj p scrut =>
      match ExAst.lookup_constructor_full Σ p.(proj_ind) 0 with
      | Some (mib, oib, (_, fields, arity)) =>
        if negb (Nat.eqb (length oib.(ExAst.ind_ctors)) 1 &&
                 Nat.eqb p.(proj_npars) mib.(ExAst.ind_npars))
        then Error "Invalid record projection" else
        let xs := local_names table ctx (map fst (skipn mib.(ExAst.ind_npars) fields)) in
        match nth_error xs p.(proj_arg) with
        | None => Error "Projection index out of bounds"
        | Some x =>
          n <- constructor_name table p.(proj_ind) 0 ;; scrut <- render ctx 1 scrut ;;
          Ok (0, "match " ++ scrut ++ " with" ++ nl ++
                 "| " ++ constructor_pattern n xs ++ " -> " ++ x)
        end
      | _ => Error "Missing projection constructor"
      end
    | EAst.tFix defs idx =>
      let names := local_names table ctx (map EAst.dname defs) in
      match nth_error names idx with
      | None => Error "Fixpoint index out of bounds"
      | Some selected =>
        ds <- traverse (fun '(n, d) =>
          let '(nas, body) := lambda_spine d.(EAst.dbody) in
          match nas with
          | [] => Error "OCaml recursive definitions must be functions"
          | _ =>
            let rec_ctx := (rev names ++ ctx)%list in
            let xs := local_names table rec_ctx nas in
            body <- render (rev xs ++ rec_ctx)%list 0 body ;;
            Ok (n ++ " " ++ join " " xs ++ " =" ++ nl ++ indent body)
          end) (combine names defs) ;;
        Ok (0, "let rec " ++ join (nl ++ "and ") ds ++ nl ++ "in" ++ nl ++ selected)
      end
    | EAst.tCoFix _ _ => Error "CoFix requires a coinductive runtime translation"
    | EAst.tPrim _ => Error "Primitive values require an OCaml runtime mapping"
    | EAst.tLazy _ | EAst.tForce _ => Error "Lazy/force requires a typed runtime translation"
    end
  end.

Definition print_term fuel Σ ctx t :=
  p <- print_expr fuel Σ (name_table Σ) ctx t ;; Ok p.2.

Definition print_inductive fuel Σ table kn (mib : ExAst.mutual_inductive_body)
  (i : nat) (oib : ExAst.one_inductive_body) : result bytestring.string :=
  let ind := mkInd kn i in
  let vars := type_parameters oib.(ExAst.ind_type_vars) in
  n <- type_name table ind ;;
  cs <- traverse (fun '(c, (_, args, arity)) =>
    if negb (Nat.eqb (length args) (mib.(ExAst.ind_npars) + arity))
    then Error "Constructor type/term arity mismatch (deargumented input?)" else
    args <- traverse (fun a => print_type_at fuel Σ table vars 2 a.2)
                     (skipn mib.(ExAst.ind_npars) args) ;;
    n <- constructor_name table ind c ;;
    Ok ("| " ++ n ++ match args with [] => "" | _ => " of " ++ join " * " args end))
    (combine (seq 0 (length oib.(ExAst.ind_ctors))) oib.(ExAst.ind_ctors)) ;;
  Ok (parameters vars ++ n ++ " =" ++ nl ++
      indent (match cs with [] => "|" | _ => join nl cs end)).

(** Match the original fully qualified kernel name, before OCaml renaming. *)
Definition allocation_attribute (kn : kername) : bytestring.string :=
  match String.index 0 "_zero_alloc" (string_of_kername kn) with
  | Some _ => "[@zero_alloc]"
  | None => ""
  end.

Fixpoint function_arity (ty : ExAst.box_type) : nat :=
  match ty with
  | ExAst.TArr _ result => S (function_arity result)
  | _ => 0
  end.

Definition print_decl fuel Σ table (entry : kername * bool * ExAst.global_decl)
  : result bytestring.string :=
  let '(kn, _, decl) := entry in
  match decl with
  | ExAst.ConstantDecl c =>
    match c.(ExAst.cst_body) with
    | None => Error ("Axiom needs an OCaml implementation: " ++ string_of_kername kn)
    | Some body =>
      n <- value_name table kn ;;
      ty <- print_type_at fuel Σ table (map type_var (seq 0 (length c.(ExAst.cst_type).1))) 0 c.(ExAst.cst_type).2 ;;
      printed <- print_expr fuel Σ table [] body ;;
      let attr := allocation_attribute kn in
      (* OxCaml requires a syntactic function, even for a function alias.
         Fresh arguments avoid shadowing the aliased global constant. *)
      let printed := match body with
        | EAst.tConst _ =>
          if eqb attr "" then printed.2 else
          let xs := local_names table []
            (repeat nAnon (function_arity c.(ExAst.cst_type).2)) in
          match xs with
          | [] => printed.2
          | _ => "fun " ++ join " " xs ++ " ->" ++ nl ++
                 indent (application printed.2 xs)
          end
        | _ => printed.2
        end in
      Ok ("let" ++ attr ++ " " ++ n ++ " : " ++ ty ++ " =" ++ nl ++ indent printed ++ nl)
    end
  | ExAst.InductiveDecl mib =>
    match mib.(ExAst.ind_finite) with
    | CoFinite => Error "Coinductive declarations require a runtime translation"
    | _ =>
      let bodies := filter (fun ib => negb ib.2.(ExAst.ind_propositional))
        (combine (seq 0 (length mib.(ExAst.ind_bodies))) mib.(ExAst.ind_bodies)) in
      ds <- traverse (fun '(i, b) => print_inductive fuel Σ table kn mib i b) bodies ;;
      Ok (match ds with [] => "" | _ => "type " ++ join (nl ++ "and ") ds ++ nl end)
    end
  | ExAst.TypeAliasDecl None => Error ("Abstract type alias: " ++ string_of_kername kn)
  | ExAst.TypeAliasDecl (Some (vs, ty)) =>
    let vars := type_parameters vs in
    n <- alias_name table kn ;; ty <- print_type_at fuel Σ table vars 0 ty ;;
    Ok ("type " ++ parameters vars ++ n ++ " = " ++ ty ++ nl)
  end.

Definition emit_ocaml_with_fuel fuel (p : ExAst.global_env * EAst.term)
  : result bytestring.string :=
  let table := name_table p.1 in
  ds <- traverse (fun entry =>
    match print_decl fuel p.1 table entry with
    | Ok s => Ok s
    | Error e => Error (string_of_kername entry.1.1 ++ ": " ++ e)
    end) (rev p.1) ;;
  main <- print_expr fuel p.1 table [] p.2 ;;
  Ok ("(* Generated from MetaRocq typed erasure. *)" ++ nl ++
      join nl ds ++ nl ++ "let extracted_main =" ++ nl ++ indent main.2 ++ nl).

(** [fuel] bounds AST nesting, not the number of declarations. *)
Definition emit_ocaml := emit_ocaml_with_fuel 4096.

End OxcamlBackend.
