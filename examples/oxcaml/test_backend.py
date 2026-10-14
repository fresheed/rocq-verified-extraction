#!/usr/bin/env python3
"""Compile and execute the OCaml actually emitted by the Gallina backend.

Requires the repository's existing Rocq dependencies and OCaml compiler.
Builds Rocq libraries in the workspace so editors can resolve their imports.
Generated OCaml sources and executables live in /tmp.
Discovers individual Rocq fixtures in cases/ and compiles each independently.
Pass a case name (e.g. basic) to run only that case; omit it to run all cases.
"""
import argparse
import pathlib
import re
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
TEST_DIR = pathlib.Path(__file__).resolve().parent
ROCQ = ("rocq", "compile", "-Q", "theories", "Malfunction",
        "-Q", "examples", "Malfunction.Examples")


def run(*args):
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f"{args!r}\n{result.stdout}\n{result.stderr}")
    return result.stdout


fixtures = sorted((TEST_DIR / "cases").glob("*.v"))
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("case", nargs="?", metavar="CASE",
                    help="case name without .v; omit to run all cases")
args = parser.parse_args()
if not fixtures:
    parser.error("No backend test cases found")
if args.case is not None:
    available = {fixture.stem: fixture for fixture in fixtures}
    if args.case not in available:
        parser.error(f"Unknown case {args.case!r}. Available cases: {', '.join(available)}")
    fixtures = [available[args.case]]

for theory in ("OxcamlBackend", "OxcamlPipeline"):
    run(*ROCQ, f"theories/{theory}.v")

run(*ROCQ, str(TEST_DIR / "test_backend.v"))

with tempfile.TemporaryDirectory(prefix="oxcaml-backend-") as tmp:
    tmp = pathlib.Path(tmp)
    for original in fixtures:
        output = run(*ROCQ, str(original))
        cases = re.findall(r"BEGIN_OCAML (\w+)\n(.*?)END_OCAML", output, re.S)
        if not cases:
            assert original.stem.startswith("rejects_"), output
            print(f"PASS {original.stem}: Rocq rejection check")
            continue
        assert len(cases) == 1, f"Expected one emitted program in {original.name}"
        name, code = cases[0]
        assert name == original.stem, f"Test label does not match {original.name}"
        true = re.search(r"\| (C_\w+_true)\b", code)
        source = tmp / f"{name}.ml"
        if name == "empty_type":
            source.write_text(code)
        else:
            assert true, code
            source.write_text(code + f"\nlet () = assert (extracted_main = {true[1]})\n")
        binary = tmp / name
        run("ocamlc", "-w", "-a", "-o", str(binary), str(source))
        run(str(binary))
        detail = "compiles" if name == "empty_type" else "compiles and evaluates to true"
        print(f"PASS {name}: generated OCaml {detail}")
