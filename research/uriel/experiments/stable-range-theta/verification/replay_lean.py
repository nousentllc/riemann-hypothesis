"""Replay the original noncancellation proof and the weakened-contract counterexample."""
import argparse
from hashlib import sha1, sha256
import json
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
PIN = "40e56bab026552e089d7afcfeff08d2defb9c005"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
LEAN = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
BASE = "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval"
CONTRACT_MODULE = BASE + ".SchurStep"
ORIGINAL_MODULE = BASE + ".BlockDeterminants.AbsNe"
ORIGINAL_BLOB = "c04ecf97717ee43cc5c397098c2f425df93548fa"
CONTEXT_BLOB = "8941c842b256473c103e2d04ef94e902534ed4b5"
DEFINITION_SHA256 = "08d4aa4c311ad0ae90069393aaf48a296de878c110f2ce71fd1e03ccf017bc5a"


def require(test, message):
    if not test:
        raise ValueError(message)


def blob(data):
    return sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def lean_path(module):
    return Path(*module.split(".")).with_suffix(".lean")


def span(text, start):
    return text[text.index(start):].split("\n\n", 1)[0] + "\n"


def read_sources(args):
    original = (HERE / "AbsNe.lean").read_bytes()
    context = (HERE / "AbsNeContract.lean").read_text()
    weak = (HERE / "WeakTail.lean").read_text()
    definition = span(context, "def AbsNe : Prop")
    require(blob(original) == ORIGINAL_BLOB, "Original proof Git blob mismatch")
    require(sha256(definition.encode()).hexdigest() == DEFINITION_SHA256,
            "Extracted original definition mismatch")
    expected_weak = definition.replace("def AbsNe", "def WeakAbsNe").replace(" < μC K →", " ≤ μC K →")
    require(expected_weak == span(weak, "def WeakAbsNe : Prop"), "Unexpected weakened contract")
    if args.source:
        full_context = (args.source / "src" / lean_path(CONTRACT_MODULE)).read_bytes()
        full_proof = (args.source / "src" / lean_path(ORIGINAL_MODULE)).read_bytes()
        require(blob(full_context) == CONTEXT_BLOB and full_proof == original,
                "Reference source does not match the pinned blobs")
        require(definition.encode() == b"".join(full_context.splitlines(keepends=True)[182:189]),
                "Source contract lines differ")
    if args.git:
        for name, oid in [(CONTRACT_MODULE, CONTEXT_BLOB), (ORIGINAL_MODULE, ORIGINAL_BLOB)]:
            path = "src/" + lean_path(name).as_posix()
            value = subprocess.check_output(["git", "-C", str(args.git), "rev-parse", PIN + ":" + path], text=True)
            require(value.strip() == oid, "Blob differs from the pinned Git tree")
    return {CONTRACT_MODULE: context.encode(), ORIGINAL_MODULE: original, "WeakTail": weak.encode()}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--sdk", type=Path, required=True, help="Lean 4.33.1 installation")
    ap.add_argument("--mathlib", type=Path, required=True, help="Git checkout with prebuilt Mathlib")
    ap.add_argument("--source", type=Path, help="Original source root containing src/")
    ap.add_argument("--git", type=Path, help="Original Git checkout containing the pinned tree")
    ap.add_argument("--selection-only", action="store_true", help="Check just the conditional finite-place lemma")
    ap.add_argument("--output", type=Path, help="Write receipt JSON to this path")
    args = ap.parse_args()
    sdk, mathlib = args.sdk.resolve(), args.mathlib.resolve()
    version = subprocess.check_output([sdk / "bin/lean", "--version"], text=True).strip()
    require("4.33.1" in version and LEAN in version, "Unexpected Lean revision")
    mathlib_head = subprocess.check_output(["git", "-C", str(mathlib), "rev-parse", "HEAD"], text=True).strip()
    require(mathlib_head == MATHLIB, "Unexpected Mathlib revision")
    sources = read_sources(args)
    report = {"original_commit": PIN, "lean_version": version, "mathlib_commit": mathlib_head,
              "original_proof_full_file_byte_identical": True,
              "definition_source_lines": [183, 189], "original_project_import_closure_rebuilt": False,
              "compiled_mathematical_context": "Pinned prebuilt Mathlib plus source-exact AbsNe definition only.",
              "original_source_compared": bool(args.source), "pinned_git_tree_compared": bool(args.git),
              "modules": {}}
    if args.selection_only:
        sources = {"TailSelection": (HERE / "TailSelection.lean").read_bytes()}
        report = {"kind": "new conditional reconstruction of finite-place selection",
                  "original_source_of_argument": "TPGTail.lean:125-140",
                  "lean_version": version, "mathlib_commit": mathlib_head,
                  "proved_automorphic_integrability": False, "modules": {}}
    with tempfile.TemporaryDirectory(prefix="theta-noncancellation-") as temp:
        root = Path(temp)
        libs = [root, mathlib / ".lake/build/lib/lean", *sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean")), sdk / "lib/lean"]
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, libs)), LEAN_SYSROOT=str(sdk),
                   PATH=str(sdk / "bin") + os.pathsep + os.environ.get("PATH", ""))

        def run(program, *arguments):
            cmd = [sdk / "bin" / program, *arguments]
            status = subprocess.run(cmd, cwd=root, env=env, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True)
            require(status.returncode == 0 and "sorryAx" not in status.stdout and
                    "declaration uses 'sorry'" not in status.stdout, status.stdout)
            return status.stdout.strip()

        for name, data in sources.items():
            path = lean_path(name)
            original = root / path
            original.parent.mkdir(parents=True, exist_ok=True)
            original.write_bytes(data)
            compiled = run("lean", "-j1", "--root=.", "-o", str(path.with_suffix(".olean")), str(path))
            declarations = {"WeakTail": ("UpperTheory.TP.absNe", "UrielCheck.weak_tail_fails"),
                            "TailSelection": ("UrielCheck.finite_places_tail",)}
            for declaration in declarations.get(name, ()):
                require("'" + declaration + "' depends on axioms: [propext, Classical.choice, Quot.sound]" in compiled,
                        "Missing expected axiom check for " + declaration)
            replay = run("leanchecker", "-v", name)
            require("replaying " + name in replay, "Missing module replay marker")
            report["modules"][name] = {"source_sha256": sha256(data).hexdigest(),
                                       "kernel_replay": replay, "compile_output": compiled}
    encoded = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    if args.output:
        args.output.write_text(encoded)
    else:
        print(encoded, end="")


if __name__ == "__main__":
    main()
