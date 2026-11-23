"""Elaborate and replay the supplementary outer-scale geometric implications."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
NAMES = ["saturation", "closedHit"]


def replay(sdk, mathlib):
    source = Path(__file__).resolve().with_name("GapGeometry.lean")
    sdk, mathlib = sdk.resolve(), mathlib.resolve()
    revision = subprocess.check_output(["git", "-C", str(mathlib), "rev-parse", "HEAD"], text=True).strip()
    if revision != MATHLIB:
        raise ValueError("Mathlib revision differs from the pinned input")
    with tempfile.TemporaryDirectory() as temp:
        cwd = Path(temp)
        shutil.copyfile(source, cwd / source.name)
        libs = [cwd, mathlib / ".lake/build/lib/lean", *sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean")), sdk / "lib/lean"]
        env = {**os.environ, "PATH":str(sdk/"bin")+os.pathsep+os.environ["PATH"], "LEAN_PATH":os.pathsep.join(map(str,libs)), "LEAN_SYSROOT":str(sdk)}
        def run(command):
            proc = subprocess.run(command,cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            if proc.returncode:
                raise RuntimeError(proc.stdout)
            return proc.stdout.strip()
        version = run([str(sdk/"bin/lean"), "--version"])
        if not version.startswith("Lean (version 4.33.1,"):
            raise ValueError(version)
        output = run([str(sdk/"bin/lean"), "--root=.", "-o", "GapGeometry.olean", "GapGeometry.lean"])
        lines = output.splitlines()
        if len(lines) != len(NAMES) or not all(line.startswith("'OuterGap."+name+"' depends on axioms:") for name,line in zip(NAMES, lines)):
            raise RuntimeError(output)
        if any("sorryAx" in line for line in lines):
            raise RuntimeError(output)
        result = run([str(sdk/"bin/leanchecker"), "-v", "GapGeometry"])
        if result != "replaying GapGeometry":
            raise ValueError(result)
        return {"lean":version,"mathlib":revision,"source_sha256":hashlib.sha256(source.read_bytes()).hexdigest(),"axioms":lines,"replay":result,"scope":"Saturation and the closed hitting interval under the stated outer-supply model, with q=J/4. Sharpness and the arithmetic application are separate written arguments."}


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain",type=Path,required=True)
    parser.add_argument("--mathlib",type=Path,required=True)
    args=parser.parse_args()
    print(json.dumps(replay(args.toolchain,args.mathlib), indent=2))
