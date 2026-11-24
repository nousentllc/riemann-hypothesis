"""Check the two conditional scalar-one controls against pinned Lean and Mathlib."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
LEAN_REVISION = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
MATHLIB_REVISION = "0df444a360eaa60ab8c11dca51a86af692955474"
NAMES = {"ScalarOne.of_frequent_growth", "ScalarOne.of_common_mass"}


def checked_output(command, **options):
    result = subprocess.run(command, capture_output=True, text=True, **options)
    log = (result.stdout + result.stderr).strip()
    if result.returncode:
        raise SystemExit(log or result.returncode)
    return log


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sdk", type=Path, required=True)
    parser.add_argument("--mathlib", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, default=HERE / "receipt.json")
    args = parser.parse_args()
    sdk, mathlib = args.sdk.resolve(), args.mathlib.resolve()
    version = checked_output([sdk / "bin/lean", "--version"])
    revision = checked_output(["git", "-C", mathlib, "rev-parse", "HEAD"])
    if LEAN_REVISION not in version or revision != MATHLIB_REVISION:
        raise SystemExit("The supplied toolchain or Mathlib revision differs from the research pin.")
    source = HERE / "ScalarOne.lean"
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        shutil.copyfile(source, root / source.name)
        libraries = [root, mathlib / ".lake/build/lib/lean",
                     *sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean")),
                     sdk / "lib/lean"]
        env = dict(os.environ, LEAN_SYSROOT=str(sdk), LEAN_PATH=os.pathsep.join(map(str, libraries)))
        checked = checked_output([sdk / "bin/lean", "-j1", "-o", "ScalarOne.olean", "ScalarOne.lean"],
                                 env=env, cwd=root)
        replayed = checked_output([sdk / "bin/leanchecker", "-v", "ScalarOne"], env=env, cwd=root)
        reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]+)\]", checked)
        axioms = {name: [item.strip() for item in values.split(",")] for name, values in reports}
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        if (set(axioms) != NAMES or any(set(values) - allowed for values in axioms.values())
                or "replaying ScalarOne" not in replayed or "sorry" in checked):
            raise SystemExit("Missing or unexpected evidence in the Lean logs:\n" + checked + "\n" + replayed)
        receipt = {
            "source_pin_traced": "40e56bab026552e089d7afcfeff08d2defb9c005",
            "scope": "Two new conditional Mathlib declarations. The automorphic comparison, lower growth, and binary limits are supplied as hypotheses.",
            "lean": version, "mathlib": revision,
            "module_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "axioms": axioms, "compiler_output": checked, "kernel_output": replayed,
        }
    args.receipt.write_text(json.dumps(receipt, indent=2) + "\n")
    print(checked)
    print(replayed)


if __name__ == "__main__":
    main()
