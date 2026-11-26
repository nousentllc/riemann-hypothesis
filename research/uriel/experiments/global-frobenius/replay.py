"""Replay the same-set Frobenius study using pinned original imports."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
LEAN = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
INTERFACE = (
    "Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations."
    "PrimesInProgressionNonempty"
)
LAYERS = [
    ["DyadicWitness", "HostArtin"],
    ["SameSetHost", "SelectorIntersection"],
    ["PrimeCutoff", "RampBudget"],
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args, cwd=None, env=None):
    proc = subprocess.run([str(item) for item in args], cwd=cwd, env=env,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output = proc.stdout.strip()
    if proc.returncode or "sorryAx" in output or "declaration uses `sorry`" in output:
        raise RuntimeError(f"{' '.join(map(str,args))}\n{output[-8000:]}")
    return output


def link(source, destination):
    os.symlink(Path(source).resolve(), destination)
    return destination


def replay_module(name, work, sdk, env, pool_source):
    filename = name + ".lean"
    src = pool_source / filename
    shutil.copyfile(src, work / filename)
    object_name = name + ".olean"
    output = run([sdk/"bin/lean", "-j1", "-o", object_name, filename], cwd=work, env=env)
    kernel = run([sdk/"bin/leanchecker", "-v", name], cwd=work, env=env)
    print(f"replayed {name}", flush=True)
    return {"module":name,"source_sha256":digest(src),
            "object_sha256":digest(work/object_name),
            "elaboration":output,"kernel":kernel}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("source", "sdk", "mathlib", "objects", "receipt"):
        parser.add_argument("--"+name, required=True, type=Path)
    args = parser.parse_args()
    source, sdk, mathlib, objects = (getattr(args,name).resolve()
                                     for name in ("source","sdk","mathlib","objects"))
    version = run([sdk/"bin/lean", "--version"])
    mathlib_commit = run(["git","rev-parse","HEAD"], cwd=mathlib)
    if LEAN not in version or mathlib_commit != MATHLIB:
        raise ValueError("Lean or Mathlib mismatch.")
    trace = json.loads((HERE/"source_trace.json").read_text())
    for entry in trace["files"]:
        if digest(source/entry["path"]) != entry["sha256"]:
            raise ValueError(f"Original source mismatch: {entry['path']}")
    with tempfile.TemporaryDirectory(prefix="global-frobenius-") as tmp:
        work = Path(tmp)
        native = work / "native"
        shutil.copytree(objects, native, copy_function=link)
        library = mathlib/".lake/build/lib/lean"
        deps = sorted((mathlib/".lake/packages").glob("*/.lake/build/lib/lean"))
        if mathlib.parent.name=="packages":
            deps += sorted(mathlib.parent.glob("*/.lake/build/lib/lean"))
        env = dict(os.environ, LEAN_SYSROOT=str(sdk),
                   LEAN_PATH=os.pathsep.join(map(str, [work,native,library,*deps])))
        rel = Path(*INTERFACE.split("."))
        leaf_root = work / "fresh-interface"
        leaf = leaf_root/rel.with_suffix(".olean")
        leaf.parent.mkdir(parents=True)
        interface_env = dict(env, LEAN_PATH=f"{leaf_root}{os.pathsep}{env['LEAN_PATH']}")
        source_file = rel.with_suffix(".lean")
        log = run([sdk/"bin/lean", "-j1", "-o", leaf, source_file],cwd=source,env=interface_env)
        kernel = run([sdk/"bin/leanchecker", "-v", INTERFACE],cwd=source,env=interface_env)
        destination = native/rel.with_suffix(".olean")
        destination.parent.mkdir(parents=True, exist_ok=True)
        # Remove only links in the temporary overlay. The supplying tree stays untouched.
        for ext in (".olean",".olean.private",".olean.server",".ir"):
            target = destination.with_suffix(ext)
            target.unlink(missing_ok=True)
            if leaf.with_suffix(ext).is_file():
                shutil.copyfile(leaf.with_suffix(ext), target)
        interface = {"module":INTERFACE,"source_sha256":digest(source/source_file),
                     "object_sha256":digest(leaf),"elaboration":log,"kernel":kernel}
        print(f"replayed {INTERFACE}",flush=True)
        modules = []
        with ThreadPoolExecutor(max_workers=2) as pool:
            for layer in LAYERS:
                modules.extend(pool.map(
                    lambda name: replay_module(name,work,sdk,env,HERE), layer))
    result = {"original":trace["commit"],"lean":version,"mathlib":mathlib_commit,
              "interface_rebuilt":interface,"modules":modules,
              "scope":"Prepared original project objects. The host supply and Linnik "
                      "are exact original proposition inputs of the combined Lean theorem; "
                      "their upstream proofs are source-traced."}
    args.receipt.write_text(json.dumps(result,indent=2)+"\n")


if __name__ == "__main__":
    main()
