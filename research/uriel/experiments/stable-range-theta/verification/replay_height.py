"""Check the original HgtCount module and a source-aligned dyadic strengthening."""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import tempfile

from replay_lean import HERE, LEAN, MATHLIB, PIN, blob, lean_path, require

ORIGINAL = "Development.WeilBound.ThetaLifts.LatticeBasics.HgtCount"
OID = "16d590ce52c928942f4278ea5aa315e3b73e6b0d"
NAMES = ["GlobalTheory.ThK.Dbl.Hgt.integrable_of_count", "UrielCheck.integrable_of_count_at",
         "UrielCheck.integrable_power_after", "UrielCheck.ratio_past_power",
         "UrielCheck.ratio_at_integer", "UrielCheck.quarter_gap"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sdk", type=Path, required=True)
    parser.add_argument("--mathlib", type=Path, required=True)
    parser.add_argument("--source", type=Path, default=HERE.parent / "original")
    parser.add_argument("--git", type=Path, help="Optional local original Git tree")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sdk, mathlib = args.sdk.resolve(), args.mathlib.resolve()
    version = subprocess.check_output([sdk / "bin/lean", "--version"], text=True).strip()
    require("4.33.1" in version and LEAN in version, "Lean pin mismatch")
    require(subprocess.check_output(["git", "-C", mathlib, "rev-parse", "HEAD"], text=True).strip()
            == MATHLIB, "Mathlib pin mismatch")
    relative = Path("src") / lean_path(ORIGINAL)
    original = (args.source / relative).read_bytes()
    enlarged = (HERE / "DyadicThreshold.lean").read_bytes()
    require(blob(original) == OID, "Original HgtCount blob differs")
    if args.git:
        expected = subprocess.check_output(["git","-C",args.git,"rev-parse",PIN + ":" + relative.as_posix()],text=True)
        require(expected.strip() == OID, "Pinned Git object differs")
    lines = original.splitlines(keepends=True)
    common = [[43, 53], [60, 75]]
    for left, right in common:
        require(b"".join(lines[left-1:right]) in enlarged, "Unchanged source proof segment differs")
    report = {"lean_version": version, "mathlib": MATHLIB, "original_pin": PIN, "original_blob": OID,
              "original_file_complete": True, "original_imports": ["Mathlib"], "source_aligned_spans": common,
              "pinned_git_tree_compared": bool(args.git), "kernel_checks": {},
              "automorphic_count_hypothesis_furnished_by_this_check": False}
    with tempfile.TemporaryDirectory(prefix="dyadic-height-") as temp:
        root = Path(temp)
        libs = [root, mathlib / ".lake/build/lib/lean", *sorted((mathlib/".lake/packages").glob("*/.lake/build/lib/lean")), sdk/"lib/lean"]
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, libs)), LEAN_SYSROOT=str(sdk),
                   PATH=str(sdk / "bin") + os.pathsep + os.environ.get("PATH", ""))
        def run(tool, *arguments):
            p = subprocess.run([sdk/"bin"/tool, *arguments], env=env, cwd=root,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            require(p.returncode == 0 and "sorryAx" not in p.stdout and
                    "declaration uses 'sorry'" not in p.stdout, p.stdout)
            return p.stdout.strip()
        for name,data in ((ORIGINAL, original), ("DyadicThreshold", enlarged)):
            path = lean_path(name)
            (root/path).parent.mkdir(parents=True, exist_ok=True)
            (root/path).write_bytes(data)
            log = run("lean", "-j1", "--root=.", "-o", str(path.with_suffix(".olean")), str(path))
            if name == "DyadicThreshold":
                for decl in NAMES:
                    require("'" + decl + "' depends on axioms: [propext, Classical.choice, Quot.sound]" in log,
                            "Axiom check missing for " + decl)
            replay = run("leanchecker", "-v", name)
            require("replaying " + name in replay, "Replay marker missing")
            report["kernel_checks"][name] = {"source_sha256":sha256(data).hexdigest(),
                                             "compile_output":log, "replay":replay}
    text = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
