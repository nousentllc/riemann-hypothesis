"""Elaborate and replay the Minkowski certificate on the full conductor-seven base field."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
NAMES = {"SevenBase": ("SlotSevenProbe", ["seven_pid","base_class_number","seven_not_dvd_class"]),
         "SevenCarries": ("SlotSevenCarry", ["unitStep","denominatorUnit","residueCertificate"])}


def replay(sdk, mathlib, module="SevenBase"):
    source = Path(__file__).resolve().with_name(module+".lean")
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
        output = run([str(sdk/"bin/lean"), "--root=.", "-o", module+".olean", module+".lean"])
        lines = output.splitlines()
        ns,names=NAMES[module]
        if len(lines) != len(names) or not all(line.startswith("'"+ns+"."+name+"' ") for name,line in zip(names,lines)):
            raise RuntimeError(output)
        allowed={"propext","Classical.choice","Quot.sound"}
        if any("sorryAx" in line or (not line.endswith("does not depend on any axioms") and
            ("depends on axioms: [" not in line or not set(line.split("[")[-1].rstrip("]").split(", ")) <= allowed)) for line in lines):
            raise RuntimeError(output)
        result = run([str(sdk/"bin/leanchecker"), "-v", module])
        if result != "replaying "+module:
            raise ValueError(result)
        return {"lean":version,"mathlib":revision,"source_sha256":hashlib.sha256(source.read_bytes()).hexdigest(),"axioms":lines,"replay":result,"scope":("The whole cyclotomic field at conductor seven has class number one." if module=="SevenBase" else "All-height normalization of the power denominator and the three mod-seven base evaluations. The full carry proof and reflection are written mathematics.")}


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain",type=Path,required=True)
    parser.add_argument("--module",choices=list(NAMES),default="SevenBase")
    parser.add_argument("--mathlib",type=Path,required=True)
    args=parser.parse_args()
    print(json.dumps(replay(args.toolchain,args.mathlib,args.module), indent=2))
