"""Compile and kernel-replay the finite fractional-dual and rational-accounting lemmas with cached Mathlib."""

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory


def replay(toolchain, mathlib):
    source = Path(__file__).resolve().with_name("Cycle64Dual.lean")
    mathlib = mathlib.resolve()
    bins = toolchain.resolve() / "bin"
    mathlib_pin = "0df444a360eaa60ab8c11dca51a86af692955474"
    commit = subprocess.check_output(["git", "-C", mathlib, "rev-parse", "HEAD"], text=True).strip()
    if commit != mathlib_pin:
        raise RuntimeError(f"Unexpected Mathlib commit {commit}")
    with TemporaryDirectory() as workname:
        work = Path(workname)
        libs = ([work, mathlib / ".lake/build/lib/lean"]
                + sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean")))
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, libs)),
                   LEAN_SYSROOT=str(toolchain.resolve()),
                   PATH=os.pathsep.join([str(bins), os.environ.get("PATH", "")]))
        def run(*args):
            proc = subprocess.run(list(args), cwd=work, env=env, text=True, capture_output=True)
            if proc.returncode or "uses 'sorry'" in proc.stderr + proc.stdout:
                raise RuntimeError(proc.stderr + proc.stdout)
            return (proc.stdout + proc.stderr).strip()
        version = run(bins / "lean", "--version")
        if "version 4.33.1" not in version:
            raise RuntimeError(version)
        (work / source.name).write_bytes(source.read_bytes())
        obj = source.stem + ".olean"
        log = run(bins / "lean", "-o", obj, source.name)
        endpoints = {"fractional_toll_bound", "rational_interior_ledger"}
        lines = re.sub(r"\n[ \t]+", " ", log).splitlines()
        names = set()
        for line in lines:
            match = re.fullmatch(r"'Cycle64Dual\.(\w+)' depends on axioms: \[(.*?)\]", line)
            if not match:
                pure = re.fullmatch(r"'Cycle64Dual\.(\w+)' does not depend on any axioms", line)
                if pure:
                    names.add(pure[1])
                    continue
                raise RuntimeError(line)
            if not set(match[2].split(', ')) <= {'propext', 'Classical.choice', 'Quot.sound'}:
                raise RuntimeError(line)
            names.add(match[1])
        if names != endpoints or len(lines) != len(endpoints):
            raise RuntimeError(log)
        expected = set(lines)
        checked = run(bins / "leanchecker", "-v", source.stem)
        if checked != "replaying " + source.stem:
            raise RuntimeError(checked)
        return {"scope": "finite weighted deficit weak dual and one rational interior rate ledger; chart enumeration and analytic transport excluded",
                "version": version, "mathlib": commit, "axioms": sorted(expected),
                "source_sha256": sha256(source.read_bytes()).hexdigest(),
                "object_sha256": sha256((work / obj).read_bytes()).hexdigest(),
                "kernel": checked}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--mathlib", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(replay(args.toolchain, args.mathlib), indent=2))


if __name__ == "__main__":
    main()
