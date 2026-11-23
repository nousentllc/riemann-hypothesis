"""Authenticate the local analytic dependency closure and replay the new theorem.

Run with Python 3.9+ and the pinned local Lean SDK, Mathlib checkout/cache, and
original sources/compiled project root identified in analytic_modules.json.
The 28 compiled hashes match the published project manifest; the matching
build recipe is in the repository's second experiment, VERIFICATION.md.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
from tempfile import TemporaryDirectory


def digest(data):
    return hashlib.sha256(data).hexdigest()


def run(cmd, env, cwd):
    return subprocess.run(cmd, env=env, cwd=cwd, check=True, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT).stdout.strip()


def replay(args):
    here = Path(__file__).resolve().parent
    index = json.loads((here / "analytic_modules.json").read_text())
    sdk = args.toolchain.resolve()
    mathlib = args.mathlib.resolve()
    original = args.source.resolve()
    project = args.objects.resolve()
    for record in index["modules"]:
        data = (original / record["source"]).read_bytes()
        object_id = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if object_id != record["git_blob"] or digest(data) != record["source_sha256"]:
            raise ValueError("Source digest differs for " + record["module"])
        if digest((project / record["olean"]).read_bytes()) != record["olean_sha256"]:
            raise ValueError("Compiled module digest differs for " + record["module"])
    revision = subprocess.check_output(["git", "-C", str(mathlib), "rev-parse", "HEAD"], text=True).strip()
    if revision != index["mathlib_pin"]:
        raise ValueError("Mathlib revision differs")
    with TemporaryDirectory() as temp:
        work = Path(temp)
        component = "WindowMass"
        shutil.copyfile(here / (component + ".lean"), work / (component + ".lean"))
        libs = [work, project, mathlib / ".lake/build/lib/lean",
                *sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean")), sdk / "lib/lean"]
        env = {**os.environ, "PATH": str(sdk/"bin") + os.pathsep + os.environ["PATH"],
               "LEAN_SYSROOT": str(sdk), "LEAN_PATH": os.pathsep.join(map(str, libs))}
        version = run([str(sdk / "bin/lean"), "--version"], env, work)
        if not version.startswith("Lean (version " + index["lean"] + ","):
            raise ValueError("Lean version differs")
        proof = run([str(sdk/"bin/lean"), "--root=.", "-o", component + ".olean",
                     component + ".lean"], env, work)
        declarations = ["integrable_density", "forced_mass", "suffix_weight", "forced_power"]
        lines = ["'Uriel.WindowMass." + name + "' depends on axioms: [propext, Classical.choice, Quot.sound]"
                 for name in declarations]
        if proof.splitlines() != lines:
            raise ValueError("Unexpected declaration or axiom inventory: " + proof)
        checked = run([str(sdk / "bin/leanchecker"), "-v", component], env, work)
        if checked != "replaying " + component:
            raise ValueError("Unexpected kernel message: " + checked)
        return {"original_pin": index["pin"], "authenticated_original_project_modules": len(index["modules"]),
                "mathlib_pin": revision, "lean": version, "supplemental_source_sha256": digest((here/(component+".lean")).read_bytes()),
                "object_sha256_this_build": digest((work/(component+".olean")).read_bytes()),
                "declarations": declarations, "axiom_inventory_each": ["propext","Classical.choice","Quot.sound"],
                "kernel_replay": checked,
                "scope":"28 pinned project sources and compiled objects authenticated. The new module was elaborated and independently kernel-replayed against these cached imports and pinned Mathlib; the arithmetic construction and the complete RH project were not rebuilt."}


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    for flag in ["toolchain", "mathlib", "source", "objects"]:
        cli.add_argument("--" + flag, type=Path, required=True)
    args = cli.parse_args()
    print(json.dumps(replay(args), indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()

