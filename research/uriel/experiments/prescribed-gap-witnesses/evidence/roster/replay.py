"""Replay the fixed-roster source extension. Print a JSON kernel receipt."""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path


def run():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--mathlib", type=Path, required=True)
    parser.add_argument("--source", type=Path, required=True,
                        help="Original source root containing Development/ and Formalism/.")
    parser.add_argument("--proof-lib", type=Path, action="append", required=True,
                        help="Precompiled original modules. Repeat to add a root.")
    args = parser.parse_args()
    lean = args.toolchain.resolve() / "bin/lean"
    checker = args.toolchain.resolve() / "bin/leanchecker"
    checkout = args.mathlib.resolve()
    source = Path(__file__).with_name("FixedRoster.lean")
    provenance = json.loads(source.with_name("source.json").read_text())
    for name, identity in provenance["source_paths_relative_to_src"].items():
        data = (args.source / name).read_bytes()
        if hashlib.sha256(data).hexdigest() != identity["sha256"]:
            raise ValueError(f"Unexpected source contents at {name}")
    revision = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"],
                                       text=True).strip()
    if revision != "0df444a360eaa60ab8c11dca51a86af692955474":
        raise ValueError(f"Unexpected Mathlib commit {revision}")
    with tempfile.TemporaryDirectory() as tmp:
        build = Path(tmp)
        shutil.copyfile(source, build / source.name)
        paths = [build, *(p.resolve() for p in args.proof_lib), checkout / ".lake/build/lib/lean",
                 *sorted((checkout / ".lake/packages").glob("*/.lake/build/lib/lean")),
                 args.toolchain.resolve() / "lib/lean"]
        env = {**os.environ, "LEAN_PATH": os.pathsep.join(map(str, paths)),
               "LEAN_SYSROOT": str(args.toolchain.resolve())}
        def call(*cmd):
            step = subprocess.run(cmd, cwd=build, env=env, text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT)
            if step.returncode:
                raise RuntimeError(step.stdout)
            return step.stdout.strip()
        version = call(lean, "--version")
        if "version 4.33.1," not in version:
            raise ValueError(version)
        output = call(lean, "--root=.", "-o", "FixedRoster.olean", source.name)
        families = re.findall(r"'(FixedRoster\.\w+)' depends on axioms: \[([^\]]*)\]", output)
        expected = {"order_one", "prime_k", "prime_one", "seven_mem", "roster_of_class_one", "slot_field"}
        if {name.split(".")[1] for name, _ in families} != expected:
            raise RuntimeError(output)
        for _, axioms in families:
            if set(axioms.split(", ")) - {"propext", "Classical.choice", "Quot.sound"}:
                raise ValueError(axioms)
        call(checker, "FixedRoster")
    return {"provider": version, "mathlib_commit": revision, "original_commit": provenance["commit"], "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "declarations": dict(families), "leanchecker_fixed_roster_exit_code": 0,
            "class_number_one": "hypothesis in roster_of_class_one; written argument in README.md",
            "visit": "new module only; imported arithmetic modules supplied as compiled prerequisites"}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
