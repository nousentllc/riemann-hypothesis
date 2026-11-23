"""Compile and kernel-replay five supplemental elementary geometric lemmas."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory

PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
NAMES = ["hit_iff", "clean_budget", "overlap_at_least", "chain_hits", "one_band_capacity"]

def verify(mathlib: Path, toolchain: Path) -> dict:
    lib = mathlib.resolve()
    sdk = toolchain.resolve()
    rev = subprocess.check_output(["git", "-C", str(lib), "rev-parse", "HEAD"], text=True).strip()
    if rev != PIN:
        raise ValueError("Mathlib revision differs")
    lean = sdk / "bin/lean"
    version = subprocess.check_output([str(lean), "--version"], text=True).strip()
    if not version.startswith("Lean (version 4.33.1,"):
        raise ValueError("Unexpected Lean version")
    with TemporaryDirectory() as temporary:
        work = Path(temporary)
        mod = "WindowGeometry"
        src = Path(__file__).resolve().parent / (mod + ".lean")
        shutil.copyfile(src, work/src.name)
        paths = [work, lib/".lake/build/lib/lean", *sorted((lib/".lake/packages").glob("*/.lake/build/lib/lean")), sdk/"lib/lean"]
        env = {**os.environ, "LEAN_PATH":os.pathsep.join(map(str, paths)), "LEAN_SYSROOT":str(sdk)}
        def invoke(args):
            p = subprocess.run(list(map(str,args)), text=True, cwd=work, env=env, capture_output=True)
            if p.returncode:
                raise RuntimeError(p.stdout+p.stderr)
            return p.stdout.strip()
        log = invoke([lean, "--root=.", "-o", mod+".olean", src.name])
        axes = ["propext", "Classical.choice", "Quot.sound"]
        expected = ["'Uriel.ExceptionalGeometry."+name+"' depends on axioms: ["+", ".join(axes)+"]" for name in NAMES]
        if log.splitlines() != expected:
            raise ValueError(log)
        checked = invoke([sdk/"bin/leanchecker", "-v", mod])
        if checked != "replaying "+mod:
            raise ValueError(checked)
        return dict(mathlib=PIN, lean=version, declarations=NAMES, axioms=axes,
                    source_sha256=hashlib.sha256((work/src.name).read_bytes()).hexdigest(), kernel=checked)

if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    for name in ("mathlib", "toolchain"):
        p.add_argument("--"+name, type=Path, required=True)
    print(json.dumps(verify(**vars(p.parse_args())), indent=2))
