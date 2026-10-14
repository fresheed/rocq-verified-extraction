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
   (*
    (* ▷ *)
   (* Check if the preconditions for dearging are valid, otherwise dearging will be the identity *)
   dearging_checks_transform_mapping econf.(dearging_config) (hastrel := eq_refl) (hastbox := eq_refl) ▷
   dearging_transform_mapping econf.(dearging_config) ▷
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
