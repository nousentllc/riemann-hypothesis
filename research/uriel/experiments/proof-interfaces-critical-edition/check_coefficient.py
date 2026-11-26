"""Compile and kernel-check the coefficient corollary against the pinned readable build."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def output(command, **kwargs):
    return subprocess.check_output(command, text=True, stderr=subprocess.STDOUT, **kwargs).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sdk", type=Path, required=True)
    parser.add_argument("--readable", type=Path, required=True)
    args = parser.parse_args()
    sdk, project = args.sdk.resolve(), args.readable.resolve()
    compiler = output([sdk / "bin/lean", "--version"])
    mathlib = output(["git", "-C", project / ".lake/packages/mathlib", "rev-parse", "HEAD"])
    pin = output(["git", "-C", project, "rev-parse", "HEAD"])
    if "eb6cafb7290e" not in compiler or mathlib != "56a005855ea17e0b0958f73ec801ae140b0a1679" or pin != "e063a923620ee7787b4a1270421478645bf66bdb":
        raise ValueError("The configured project, compiler or Mathlib differs from the release.")
    source = Path(__file__).with_name("Coefficient.lean")
    with tempfile.TemporaryDirectory() as temp:
        work = Path(temp)
        shutil.copyfile(source, work / source.name)
        libraries = [work, project / ".lake/build/lib/lean", *sorted((project / ".lake/packages").glob("*/.lake/build/lib/lean")), sdk / "lib/lean"]
        env = dict(os.environ, LEAN_SYSROOT=str(sdk), LEAN_PATH=os.pathsep.join(map(str, libraries)))
        try:
            log = output([sdk / "bin/lean", "-j1", "-o", "Coefficient.olean", source.name], cwd=work, env=env)
            checked = output([sdk / "bin/leanchecker", "-v", "Coefficient"], cwd=work, env=env)
        except subprocess.CalledProcessError as err:
            raise SystemExit(err.output) from err
        if "'NousInterfaces.chosen_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound]" not in log or "sorry" in log:
            raise ValueError(log)
        obj = hashlib.sha256((work / "Coefficient.olean").read_bytes()).hexdigest()
    print(json.dumps(dict(project=pin, compiler=compiler, mathlib=mathlib, source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(), object_sha256=obj, elaboration=log, kernel=checked), indent=2))


if __name__ == "__main__":
    main()
