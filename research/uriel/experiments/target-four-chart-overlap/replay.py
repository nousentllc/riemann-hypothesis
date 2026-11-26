"""Reproduce integer checks and optionally rebuild and kernel-replay the overlap theorems."""
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
MODULES = ["PivotOverlap", "OverlapMeasure", "OverlapVolume", "OverlapEndpoint", "TwoSlabs", "FoldImage", "WideSheets"]
PRIOR = ["TargetFourHaar", "FourChart", "FourBoxMeasures"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(args, work, env):
    p = subprocess.run(args, cwd=work, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if p.returncode or "sorryAx" in p.stdout:
        raise RuntimeError(str(args) + "\n" + p.stdout)
    return p.stdout.strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true")
    for opt in ["sdk","mathlib","study","objects","previous","receipt"]:
        parser.add_argument("--"+opt,type=Path)
    parser.add_argument("--prior-objects",nargs="+",type=Path)
    args=parser.parse_args()
    data=json.loads(subprocess.check_output([sys.executable,"-B",ROOT/"overlap.py"]))
    if data != json.loads((ROOT/"results.json").read_text()):
        raise ValueError("Finite evidence differs")
    print("Reproduced finite fibers, coupled tests, weights and fold controls.",flush=True)
    wide=json.loads(subprocess.check_output([sys.executable,"-B",ROOT/"wide.py"]))
    if wide != json.loads((ROOT/"wide_results.json").read_text()):
        raise ValueError("Six-coordinate wide-box counts differ")
    print("Reproduced wide-box counts for every target at five depths.",flush=True)
    if not args.lean:
        return
    if not all([args.sdk,args.mathlib,args.study,args.objects,args.previous]):
        parser.error("--lean requires --sdk, --mathlib, --study, --objects and --previous")
    sdk,lib,previous=args.sdk.resolve(),args.mathlib.resolve(),args.previous.resolve()
    version=subprocess.check_output([sdk/"bin/lean","--version"],text=True).strip()
    rev=subprocess.check_output(["git","-C",lib,"rev-parse","HEAD"],text=True).strip()
    if "819816b2e0a3" not in version or rev!="0df444a360eaa60ab8c11dca51a86af692955474":
        raise ValueError("Unexpected compiler or Mathlib revision")
    pins=json.loads((ROOT/"inputs.json").read_text())
    result=dict(compiler=version,mathlib=rev,prior_commit=pins["previous_commit"],
                mode="published objects" if args.prior_objects else "recompiled prior source",
                inputs={},modules=[],finite_sha256=digest(ROOT/"results.json"), wide_sha256=digest(ROOT/"wide_results.json"))
    with tempfile.TemporaryDirectory() as tmp:
        work=Path(tmp)
        paths=[work,args.study.resolve(),args.objects.resolve(),lib/".lake/build/lib/lean",
               *sorted((lib/".lake/packages").glob("*/.lake/build/lib/lean")),sdk/"lib/lean"]
        env=dict(os.environ,LEAN_SYSROOT=str(sdk),LEAN_PATH=os.pathsep.join(map(str,paths)))
        for name in PRIOR:
            src=previous/(name+".lean")
            if digest(src)!=pins[name]["source_sha256"]:
                raise ValueError("Unexpected prior source for "+name)
            obj=work/(name+".olean")
            if args.prior_objects:
                found=next((p/obj.name for p in args.prior_objects if (p/obj.name).is_file()),None)
                if found is None or digest(found)!=pins[name]["object_sha256"]:
                    raise ValueError("Unexpected cached input for "+name)
                shutil.copyfile(found,obj)
            else:
                shutil.copyfile(src,work/src.name)
                command([sdk/"bin/lean","-j1","-o",obj.name,src.name],work,env)
            result["inputs"][name]=digest(obj)
        for name in MODULES:
            src=ROOT/(name+".lean")
            shutil.copyfile(src,work/src.name)
            cmd=["-j1","-o",name+".olean",src.name]
            output=command([sdk/"bin/lean",*cmd],work,env)
            pairs={n:v.split(", ") for n,v in re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]",output)}
            pairs.update({n:[] for n in re.findall(r"'([\w.]+)' does not depend on any axioms",output)})
            expected=set(re.findall(r"^#print axioms ([\w.]+)", src.read_text(),re.M))
            if set(pairs)!=expected or not expected or any(set(v)-ALLOWED for v in pairs.values()):
                raise ValueError("Axiom audit failed for "+name)
            print("Elaborated",name,flush=True)
            audit=command([sdk/"bin/leanchecker","-v",name],work,env)
            if "replaying "+name not in audit:
                raise ValueError("Absent replay confirmation for "+name)
            result["modules"].append(dict(name=name,source_sha256=digest(src),object_sha256=digest(work/(name+".olean")),
                elaboration_exit=0,checker_exit=0,elaboration=output,replay=audit,axioms=pairs))
            print("Kernel replayed",name,flush=True)
    payload=json.dumps(result,indent=2)+"\n"
    if args.receipt:
        args.receipt.write_text(payload)
    else:
        print(payload)


if __name__=="__main__":
    main()
