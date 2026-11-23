"""Rebuild the finite-measure supplement with the pinned Lean and Mathlib setup."""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryDirectory


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("checkout", "toolchain", "mathlib"):
        parser.add_argument("--"+name, required=True, type=lambda s: Path(s).resolve())
    args = parser.parse_args()
    sys.path.insert(0, str(args.checkout / "research/uriel/experiments/joint-witness"))
    from build_original import FLAGS, environment
    env, version = environment(args.toolchain, args.mathlib)
    file = Path(__file__).with_name("PrimeMassSecants.lean")
    with TemporaryDirectory() as tmp:
        work = Path(tmp)
        (work / file.name).write_bytes(file.read_bytes())
        env["LEAN_PATH"] = str(work) + os.pathsep + env["LEAN_PATH"]
        compiler = subprocess.run([args.toolchain/"bin/lean", *FLAGS, "--root=.", "-o",
                                   file.with_suffix(".olean").name, file.name],
                                  cwd=work, env=env, capture_output=True, text=True)
        if compiler.returncode:
            raise RuntimeError(compiler.stdout + compiler.stderr)
        checker = subprocess.check_output([args.toolchain/"bin/leanchecker", "-v", file.stem],
                                          cwd=work, env=env, text=True, stderr=subprocess.STDOUT)
        log = re.sub(r"\n[ \t]+", " ", (compiler.stdout + compiler.stderr).strip()).splitlines()
        names = ("left_atom", "right_atom", "cumulative_bracket", "triangular_atom", "bracket_width")
        expected = {f"'Uriel.PrimeMass.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                    for name in names}
        if set(log) != expected or len(log) != len(names):
            raise ValueError(compiler.stdout + compiler.stderr)
        if checker.strip() != "replaying " + file.stem:
            raise ValueError(checker)
        print(json.dumps({"module":file.stem, "supplement_sha256":sha256(file.read_bytes()).hexdigest(),
                          "object_sha256":sha256((work/file.with_suffix(".olean").name).read_bytes()).hexdigest(),
                          "toolchain":version, "flags":FLAGS, "axioms":log,"kernel":checker.strip()}, indent=2))


if __name__=="__main__":
    main()
