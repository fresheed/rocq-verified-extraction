(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Common Require Import Transform config.
From MetaRocq.Utils Require Import bytestring utils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICTyping PCUICReduction PCUICAstUtils PCUICSN
    PCUICTyping PCUICProgram PCUICFirstorder PCUICEtaExpand.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaRocq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EImplementBox EPretty Extract.
From MetaRocq Require Import ETransform EConstructorsAsBlocks.
From MetaRocq.Erasure Require Import EWcbvEvalNamed.
From MetaRocq.ErasurePlugin Require Import Erasure ErasureCorrectness.
From Malfunction Require Import CompileCorrect SemanticsSpec FFI Pipeline.
From Malfunction Require Import OxcamlBackend.
From CeresBS Require Import CeresSerialize.
Import PCUICProgram.
(* Import TemplateProgram (template_eta_expand).
 *)
Import PCUICTransform (template_to_pcuic_transform, pcuic_expand_lets_transform).

Import Transform.Transform.
#[local] Arguments transform : simpl never.

#[local] Obligation Tactic := program_simpl.

#[local] Existing Instance extraction_checker_flags.

#[local] Existing Instance extraction_normalizing.

Import EWcbvEval.


From MetaRocq.Erasure Require Import EWellformed EProgram EBeta.

Section Dearging.
  Import Optimize OptimizeCorrectness.

  Definition dearg (p : (option dearg_set × ExAst.global_env) * EAst.term) : ExAst.global_env * EAst.term :=
    match p.1.1 with
    | Some masks => (dearg_env masks p.1.2, dearg_term masks p.2)
    | None => (p.1.2, p.2)
    end.

  Program Definition dearging_transform_keep_types (efl := all_env_flags) cf :
    Transform.t 
      (option dearg_set × ExAst.global_env) ExAst.global_env
      EAst.term EAst.term _ _ 
      (eval_typed_eprogram_masks opt_wcbv_flags) (eval_typed_eprogram opt_wcbv_flags) :=
    {| name := "dearging";
      transform p _ := dearg p ;
      pre p := post_dearging_checks efl cf p;
      post p := let ep := (ExAst.trans_env p.1, p.2) in
        wf_eprogram efl ep /\ EEtaExpandedFix.expanded_eprogram ep ;
      obseq p hp p' v v' := v' = (dearg (p.1, v)).2 |}.
  Next Obligation.
  Proof.
    (* Forgetting the retained types gives exactly the original transform. *)
    destruct input as [[masks env] t]. destruct masks;
      exact (correctness (ETransform.dearging_transform cf) _ p).
  Qed.
  Next Obligation.
  Proof.
    intros [[masks env] t] v pr ev. destruct masks;
      exact (preservation (ETransform.dearging_transform cf) _ v pr ev).
  Qed.

End Dearging.

From MetaRocq.Erasure Require Import EReorderCstrs.

Program Definition dearging_transform_mapping_keep_types (cf : ETransform.dearging_config) :
  Transform.t _ _ _ _ _ _ (eval_typed_eprogram_masks_mapping opt_wcbv_flags) (eval_typed_eprogram_mapping opt_wcbv_flags) :=
  let tr := (dearging_transform_keep_types cf) in
 {| name := name tr;
    pre p := wf_inductives_mapping (ExAst.trans_env p.2.1.2) p.1 /\ pre tr p.2 ;
    transform p hp := let nhs := proj2 hp in (p.1, transform tr p.2 nhs) ;
    post p := wf_inductives_mapping (ExAst.trans_env p.2.1) p.1 /\ post tr p.2;
    obseq p hp p' := obseq tr p.2 (proj2 hp) p'.2 |}.
Next Obligation.
Proof.
  destruct input as [mapping [[masks env] t]]. destruct masks;
    exact (correctness (Erasure.dearging_transform_mapping cf) _ (conj i p)).
Qed.
Next Obligation.
Proof.
  intros [mapping [[masks env] t]] v pr ev. destruct masks;
    exact (preservation (Erasure.dearging_transform_mapping cf) _ v pr ev).
Qed.


(** ***********************)
Section BetaredTyped.

Print ExAst.box_type.
Definition betared_in_typed_constant_body (cst: ExAst.constant_body): ExAst.constant_body :=
  let '(ExAst.Build_constant_body tp body) := cst in
  ExAst.Build_constant_body tp (option_map betared body).

Definition betared_in_typed_decl (d: ExAst.global_decl) :=
  match d with
  | ExAst.ConstantDecl cst => ExAst.ConstantDecl (betared_in_typed_constant_body cst)
  | _ => d
  end.

Definition betared_typed_env (Σ : ExAst.global_env) : ExAst.global_env :=
  map (fun '((kn, b), decl) => ((kn, b), betared_in_typed_decl decl)) Σ.

Definition betared_program_typed (p : ExAst.global_env × EAst.term) : ExAst.global_env × EAst.term :=
  (betared_typed_env p.1, betared p.2).

(* TODO: use above *)
Definition trans_eprog (p: inductives_mapping × (ExAst.global_env × EAst.term)): eprogram :=
  (ExAst.trans_env p.2.1, p.2.2).

Axiom trust_betared_program_typed_wf :
  forall efl : EEnvFlags,
  WcbvFlags ->
  forall (input : Transform.program _ _),
  wf_eprogram efl (trans_eprog input) -> 
  wf_eprogram efl (trans_eprog (input.1, (betared_program_typed input.2))).
Axiom trust_betared_pres_typed :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) (p : Transform.program _ _)
  (v : EAst.term),
  wf_eprogram efl (trans_eprog p) ->
  eval_typed_eprogram_mapping wfl p v ->
  exists v' : EAst.term,
  eval_typed_eprogram_mapping wfl (p.1, (betared_program_typed p.2)) v' /\ v' = betared v.

Program Definition betared_transformation_keep_types (efl : EEnvFlags) (wfl : WcbvFlags) :
  Transform.t _ _ (ExAst.global_env × EAst.term) (ExAst.global_env × EAst.term) _ _
    (eval_typed_eprogram_mapping wfl) (eval_typed_eprogram_mapping wfl) :=
  {| name := "betared ";
    transform '(inds, p) _ := (inds, betared_program_typed p);
    pre p := wf_eprogram efl (trans_eprog p);
    post p := wf_eprogram efl (trans_eprog p) ;
    (* wf_inductives_mapping (ExAst.trans_env p.2.1) p.1 /\ post tr p.2; *)
    obseq p hp p' v v' := v' = betared v |}.

Next Obligation.
Proof.
  destruct input.
  now apply trust_betared_program_typed_wf in p.  
Qed.
Next Obligation.
  intros [inds ] v WF EVAL.
  by eapply trust_betared_pres_typed in EVAL as [??]; eauto.
Qed.

End BetaredTyped.



(** *******************)
Program Definition verified_typed_erasure_pipeline_oxcaml
  (efl := EWellformed.all_env_flags)
  (econf: erasure_configuration)
  (* :
  Transform.t _ _ _ _ _ _
   eval_pcuic_program_mapping
   (EProgram.eval_eprogram final_wcbv_flags) *)
    :=
   (* a bunch of nonsense for normalization preconditions *)
   let K ty (T : ty -> _) p
     := let p := T p in
        (PCUICTyping.wf_ext p -> PCUICSN.NormalizationIn p) /\
          (PCUICTyping.wf_ext p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p) in
   let T1 (p:global_env_ext_map) := p in
   (* Branches of cases are expanded to bind only variables, constructor types are expanded accordingly *)
   pcuic_expand_lets_transform_mapping (K _ T1) ▷
   (* Erasure of proofs terms in Prop and types *)
   typed_erase_transform_mapping ▷
   (* Remove match on box early for dearging *)
   remove_match_on_box_typed_transform_mapping (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl)
    ▷ 
   (* Check if the preconditions for dearging are valid, otherwise dearging will be the identity *)   
   dearging_checks_transform_mapping econf.(dearging_config) (hastrel := eq_refl) (hastbox := eq_refl)
   ▷   
   dearging_transform_mapping_keep_types econf.(dearging_config)
   ▷
   betared_transformation_keep_types all_env_flags opt_wcbv_flags
   
   (*▷
   rebuild_wf_env_transform_mapping true true ▷
   verified_lambdabox_typed_pipeline econf. *)
   .
Final Obligation.
  unfold pre_remove_match_on_box_typed. split; intuition eauto.
Qed.
(** *******************)

Program Definition typed_oxcaml_pipeline
  (config : malfunction_pipeline_config) :
  Transform.t _ _ _ _ _ _ eval_template_program_mapping
    (eval_typed_eprogram_mapping (disable_prop_cases default_wcbv_flags)) :=
  pre_erasure_pipeline_mapping ▷
  verified_typed_erasure_pipeline_oxcaml config.
Fail Next Obligation.

(** Native OCaml output, or an explicit diagnostic for unsupported input.
    Like the existing Malfunction entry point, this trusts the Rocq kernel
    for the input precondition; the backend itself is not verified. *)
Definition compile_oxcaml_gen config (p : Ast.Env.program)
  : OxcamlBackend.result bytestring.string :=
  let p' := run (typed_oxcaml_pipeline config)
    (config.(reorder_cstrs), p) (trust_coq_kernel config p) in
  OxcamlBackend.emit_ocaml p'.2.

Definition compile_oxcaml := compile_oxcaml_gen default_malfunction_config.

Definition print_oxcaml_result
    (p : EProgram.inductives_mapping * (ExAst.global_env * EAst.term))
    : bytestring.string :=
    EPretty.print_program (ExAst.trans_env p.2.1, p.2.2).

(** Debug text has no executable semantics of its own. Relate it to the
    evaluation of a typed program that prints to that text. This does not
    assert that printing is injective or that the text can be parsed back.
    The unit environment accommodates Transform's environment/term pair. *)
Definition eval_printed_oxcaml_result (fl : WcbvFlags)
  (printed : unit * bytestring.string) (v : EAst.term) : Prop :=
  exists p, printed = (tt, print_oxcaml_result p) /\
    eval_typed_eprogram_mapping fl p v.

Definition print_oxcaml_transform (fl : WcbvFlags) :
  Transform.t _ _ _ _ _ _
    (eval_typed_eprogram_mapping fl) (eval_printed_oxcaml_result fl).
Proof.
  refine {| name := "Print Oxcaml debug result"%bs;
            pre := fun _ => True;
            transform := fun p _ => (tt, print_oxcaml_result p);
            post := fun _ => True;
            obseq := fun _ _ _ v v' => v = v' |}.
  - intros; exact I.
  - intros p v _ ev. exists v. split.
    + exists p. split; [reflexivity | exact ev].
    + reflexivity.
Defined.

Program Definition oxcaml_pipeline
  (config : malfunction_pipeline_config) :
  Transform.t _ _ _ _ _ _ eval_template_program_mapping
             (eval_printed_oxcaml_result (disable_prop_cases default_wcbv_flags)) :=
  typed_oxcaml_pipeline config ▷
  print_oxcaml_transform (disable_prop_cases default_wcbv_flags)
  .

Definition debug_oxcaml (p : Ast.Env.program) : bytestring.string :=
(run (oxcaml_pipeline default_malfunction_config)
        (default_malfunction_config.(reorder_cstrs), p)
        (trust_coq_kernel default_malfunction_config p)).2.

Definition example (n : nat) := S n.

MetaRocq Quote Recursively Definition quoted_example := example.
 
Eval vm_compute in compile_oxcaml quoted_example.
