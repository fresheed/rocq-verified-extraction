## Installation and testing

```sh
opam switch create rocq-extraction --packages="ocaml-variants.4.14.2+options,ocaml-option-flambda"
eval "$(opam env --switch=rocq-extraction --set-switch)"
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-core.9.1.1 rocq-stdlib.9.0.0
opam install . --deps-only
make -j 4
```

The OCaml source backend tests additionally require Python 3. After building
the project, run all cases or a single one; for the latter case, you can
additionally save the extracted OCaml code:

```sh
python3 examples/oxcaml/test_backend.py
python3 examples/oxcaml/test_backend.py two_ptr
python3 examples/oxcaml/test_backend.py two_ptr -o /tmp/two_ptr.ml
```

The script compiles and runs the emitted OCaml using `ocamlc`.

The OxCaml backend emits `let[@zero_alloc]` for a generated definition when its
fully qualified Rocq kernel name contains `_zero_alloc` (including in a module
name).

To run OxCaml on the generated `.ml` sources, follow instructions at `https://github.com/fresheed/extraction-alloc`.