"""Replay the literal readable chart and the field-algebra bridge from verified cached imports."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

from replay import ROOT, digest, execute, module, write_result

TOP = "Lib.General.Measure.QuadricDisintegration"
PIN = "e063a923620ee7787b4a1270421478645bf66bdb"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--sdk", type=Path, required=True)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    repo, sdk = args.repo.resolve(), args.sdk.resolve()
    revision = subprocess.check_output(["git","-C",repo,"rev-parse","HEAD"],text=True).strip()
    if revision != PIN:
        raise ValueError("Unexpected readable source")
    subprocess.run(["git","-C",repo,"diff","--quiet","HEAD","--","src","lean-toolchain","lake-manifest.json"],check=True)
    version = subprocess.check_output([sdk/"bin/lean","--version"],text=True).strip()
    lib = repo/".lake/packages/mathlib"
    lp = subprocess.check_output(["git","-C",lib,"rev-parse","HEAD"],text=True).strip()
    if "4.35.0," not in version or lp != "56a005855ea17e0b0958f73ec801ae140b0a1679":
        raise ValueError("Unexpected toolchain or Mathlib")
    inputs = json.loads((ROOT/"readable_inputs.json").read_text())
    with tempfile.TemporaryDirectory() as temp:
        work = Path(temp)
        for n, h in inputs.items():
            rel = Path(n.replace(".","/"))
            f = (repo/"src"/rel).with_suffix(".lean")
            if digest(f) != h["source"]:
                raise ValueError("Changed source " + n)
            if n == TOP:
                continue
            obj = (repo/".lake/build/lib/lean"/rel).with_suffix(".olean")
            if digest(obj) != h["cached_olean"]:
                raise ValueError("Use the exact published cache for " + n)
            dest = (work/rel).with_suffix(".olean")
            dest.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(obj,dest)
        paths = [work,*sorted((repo/".lake/packages").glob("*/.lake/build/lib/lean")),sdk/"lib/lean"]
        env = dict(os.environ,LEAN_SYSROOT=str(sdk),LEAN_PATH=os.pathsep.join(map(str,paths)))
        rel = Path(TOP.replace(".","/"))
        obj = (work/rel).with_suffix(".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        cmd = ["lean","-j1","--tstack=400000","-o",str(obj),str(rel)+".lean"]
        built = execute(sdk,cmd,repo/"src",env)
        built["command"][4] = str(rel)+".olean"
        verify = execute(sdk,["leanchecker","-v",TOP],work,env)
        print("Elaborated and kernel replayed the pinned upstream chart",flush=True)
        mods = [module(sdk,n,work,env) for n in ["GaussianFrame","ReadableFourChart","ReadableIdentityChart"]]
        write_result(dict(compiler=version,mathlib=lp,readable=revision, reused_imports=len(inputs)-1,
                          imported_manifest_sha256=digest(ROOT/"readable_inputs.json"),
                          upstream=dict(module=TOP,source_sha256=inputs[TOP]["source"],object_sha256=digest(obj),
                                        commands=[built,verify]),modules=mods),args.receipt)


if __name__ == "__main__":
    main()
