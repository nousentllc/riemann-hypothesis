"""Repeat the finite experiment and optionally replay the original-edition chart modules."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
ALLOW = {"propext", "Classical.choice", "Quot.sound"}


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def execute(sdk, cmd, cwd, env):
    log = subprocess.run([sdk / "bin" / cmd[0], *cmd[1:]], cwd=cwd, env=env, text=True,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if log.returncode or "sorryAx" in log.stdout:
        raise RuntimeError(f"{cmd}\n{log.stdout}")
    return {"command": [str(s) for s in cmd], "exit": log.returncode, "output": log.stdout.strip()}


def module(sdk, name, work, env):
    source = ROOT / (name + ".lean")
    shutil.copyfile(source, work / source.name)
    run = execute(sdk, ["lean", "-j1", "-o", name + ".olean", source.name], work, env)
    wanted = set(re.findall(r"^#print axioms ([\w.]+)", source.read_text(), re.M))
    out = run["output"]
    pairs = {k: v.split(", ") for k, v in re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", out)}
    pairs.update({k: [] for k in re.findall(r"'([\w.]+)' does not depend on any axioms", out)})
    if set(pairs) != wanted or any(set(v) - ALLOW for v in pairs.values()):
        raise ValueError(f"Query mismatch for {name}: {pairs}")
    print("Elaborated", name, flush=True)
    check = execute(sdk, ["leanchecker", "-v", name], work, env)
    if "replaying " + name not in check["output"]:
        raise ValueError("Missing replay record for " + name)
    print("Kernel replayed", name, flush=True)
    return dict(module=name, source_sha256=digest(source), object_sha256=digest(work/(name+".olean")),
                queries=pairs, commands=[run, check])


def write_result(result, target):
    value = json.dumps(result, indent=2) + "\n"
    if target:
        target.write_text(value)
    else:
        print(value)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--lean", action="store_true")
    for param in ["sdk", "mathlib", "study", "objects", "receipt"]:
        p.add_argument("--" + param, type=Path)
    a = p.parse_args()
    data = json.loads(subprocess.check_output([sys.executable, "-B", ROOT/"boxes.py"]))
    if data != json.loads((ROOT/"boxes.json").read_text()):
        raise ValueError("Finite counts changed")
    print("Reproduced 100 records and the full 4096-child census.", flush=True)
    images = json.loads(subprocess.check_output([sys.executable, "-B", ROOT/"parameters.py"]))
    if images != json.loads((ROOT/"parameter_images.json").read_text()):
        raise ValueError("Readable chart image data changed")
    print("Reproduced seven parameter-image tests and the restricted-skew negative control.", flush=True)
    if not a.lean:
        return
    if not all([a.sdk, a.mathlib, a.study, a.objects]):
        p.error("--lean requires --sdk, --mathlib, --study and --objects")
    sdk, lib = a.sdk.resolve(), a.mathlib.resolve()
    ver = subprocess.check_output([sdk/"bin/lean","--version"], text=True).strip()
    pin = subprocess.check_output(["git","-C",lib,"rev-parse","HEAD"],text=True).strip()
    if "819816b2e0a3" not in ver or pin != "0df444a360eaa60ab8c11dca51a86af692955474":
        raise ValueError("Unexpected compiler or Mathlib")
    names = ["TargetFourHaar","FourChart","GaussianFrame","FourBoxMeasures","FourBoxEndpoints","FourFramePivot"]
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        paths = [work,a.study.resolve(),a.objects.resolve(),lib/".lake/build/lib/lean",
                 *sorted((lib/".lake/packages").glob("*/.lake/build/lib/lean")),sdk/"lib/lean"]
        env = dict(os.environ, LEAN_SYSROOT=str(sdk),LEAN_PATH=os.pathsep.join(map(str,paths)))
        mods = [module(sdk,name,work,env) for name in names]
    imported = ["DilateStableOddAll","DilateEndpoint","RamFieldIntegers","RamBasePivot"]
    write_result(dict(compiler=ver,mathlib=pin, original="40e56bab026552e089d7afcfeff08d2defb9c005",
                      study="17263859a4d27c62cfc67571737355f61a080806",
                      imported={n:digest(a.study/(n+".olean")) for n in imported},
                      counts_sha256=digest(ROOT/"boxes.json"),modules=mods),a.receipt)


if __name__ == "__main__":
    main()
