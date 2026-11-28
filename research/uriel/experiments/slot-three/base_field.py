"""Check the bottom field's class number and primitive root levels against pinned Mathlib."""
import argparse
from hashlib import sha256
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "joint-witness"))
from build_original import FLAGS, PIN, dump, environment, pinned_source, pinned_tree

BASE = "BaseField"
TARGETS = ("class_number", "three_not_dvd_class_card", "root_powers", "maximal_level")
CZERO_PATH = "src/Development/AutomorphicArithmetic/AutomorphicVarieties/NumberFieldTowers/XTwApplyApply.lean"


def check(args):
    toolchain = args.toolchain.resolve()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    env, versions = environment(toolchain, args.mathlib.resolve())
    env["LEAN_PATH"] = str(work) + os.pathsep + env["LEAN_PATH"]
    data = (HERE / (BASE + ".lean")).read_bytes()
    (work / (BASE + ".lean")).write_bytes(data)
    obj = work / (BASE + ".olean")
    tree = pinned_tree()
    cdef = next(line for line in pinned_source(CZERO_PATH, args.source.resolve(), tree).splitlines()
                if line.startswith(b"def cZero "))
    if cdef.decode() != "def cZero : ℕ := sSup {c : ℕ | ∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)}":
        raise ValueError("Original cZero body differs")

    def run(args):
        p = subprocess.run(args, cwd=work, env=env, capture_output=True, text=True)
        output = (p.stdout+p.stderr).strip()
        if p.returncode or "sorryAx" in output or "declaration uses 'sorry'" in output:
            raise RuntimeError(output)
        return output

    log = run([toolchain / "bin/lean", *FLAGS, "--root=.", "-o", obj, BASE + ".lean"])
    axioms = {}
    for name in TARGETS:
        m = re.search(r"'SlotThree\.BaseField\." + name + r"' depends on axioms: \[([^\]]*)\]", log)
        if not m or set(m.group(1).split(", ")) - {"propext", "Classical.choice", "Quot.sound"}:
            raise RuntimeError(log)
        axioms[name] = sorted(m.group(1).split(", "))
    replay = run([toolchain / "bin/leanchecker", "-v", BASE])
    if replay != "replaying " + BASE:
        raise RuntimeError(replay)
    dump(args.out, dict(pin=PIN, toolchain=versions, flags=FLAGS,
                        source_sha256=sha256(data).hexdigest(), olean_sha256=sha256(obj.read_bytes()).hexdigest(),
                        cZero_original_path=CZERO_PATH, cZero_original_blob=tree[CZERO_PATH],
                        cZero_original_definition=cdef.decode(), axioms=axioms,
                        compiler_output=log, kernel_replay=replay))
    print(f"Replayed {BASE} and audited all {len(axioms)} declarations.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("source", "toolchain", "mathlib", "work", "out"):
        parser.add_argument("--"+key, type=Path, required=True)
    check(parser.parse_args())
