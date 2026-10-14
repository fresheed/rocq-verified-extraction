(* Shared test infrastructure; individual fixtures live in cases/.
   Run with: python3 examples/oxcaml/test_backend.py *)
From MetaRocq.Template Require Export All.
From Malfunction Require Export OxcamlBackend OxcamlPipeline.
From Stdlib Require Export List Bool Arith.
Import ListNotations MonadNotation.
Open Scope bs_scope.

Definition emit_test {A : Type} (label : bytestring.string) (a : A) :=
  p <- tmQuoteRec a ;;
  code <- tmEval lazy (compile_oxcaml p) ;;
  match code with
  | OxcamlBackend.Ok text =>
    tmMsg ("BEGIN_OCAML " ++ label ++ OxcamlBackend.nl ++ text ++ "END_OCAML")
  | OxcamlBackend.Error error => tmFail error
  end.

(* Negative fixtures must fail explicitly, rather than emitting placeholders. *)
Definition expect_error {A} (r : OxcamlBackend.result A) :=
  match r with OxcamlBackend.Error _ => true | _ => false end.
