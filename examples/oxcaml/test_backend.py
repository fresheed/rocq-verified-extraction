#!/usr/bin/env python3
"""Compile and execute the OCaml actually emitted by the Gallina backend.

Requires the repository's existing Rocq dependencies and OCaml compiler.
Rebuilds the backend and pipeline; generated fixture artifacts live in /tmp.
Discovers individual Rocq fixtures in cases/ and compiles each independently.
"""
import pathlib
import re
import shutil
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
TEST_DIR = pathlib.Path(__file__).resolve().parent


def run(*args):
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f"{args!r}\n{result.stdout}\n{result.stderr}")
    return result.stdout


for theory in ("OxcamlBackend", "OxcamlPipeline"):
    run("rocq", "compile", "-Q", "theories", "Malfunction", f"theories/{theory}.v")

with tempfile.TemporaryDirectory(prefix="oxcaml-backend-") as tmp:
    tmp = pathlib.Path(tmp)
    infrastructure = tmp / "test_backend.v"
    shutil.copyfile(TEST_DIR / "test_backend.v", infrastructure)
    rocq = ("rocq", "compile", "-Q", "theories", "Malfunction",
            "-Q", str(tmp), "Malfunction.Examples.oxcaml")
    run(*rocq, str(infrastructure))
    fixtures = sorted((TEST_DIR / "cases").glob("*.v"))
    assert fixtures, "No backend test cases found"
    (tmp / "cases").mkdir()
    for original in fixtures:
        fixture = tmp / "cases" / original.name
        shutil.copyfile(original, fixture)
        output = run(*rocq, str(fixture))
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
