"""Replay the principal imported project modules independently of the supplement."""
import argparse, json, os, shutil, subprocess, sys
from pathlib import Path

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for label in ("mathlib","toolchain","work"):
        parser.add_argument("--"+label,type=Path,required=True)
    args=parser.parse_args()
    sdk=args.toolchain.resolve()
    lib=args.mathlib.resolve()
    work=args.work.resolve()
    env = dict(os.environ,LEAN_SYSROOT=str(sdk),PATH=str(sdk/"bin")+os.pathsep+os.environ["PATH"])
    env["LEAN_PATH"] = os.pathsep.join(map(str,[work/"lib",lib/".lake/build/lib/lean",
                                          *sorted((lib/".lake/packages").glob("*/.lake/build/lib/lean")),sdk/"lib/lean"]))
    prefix = "Development.AutomorphicArithmetic.AutomorphicVarieties."
    names=[prefix+name for name in ("LayeredIsomorphisms.PartA","LayeredIsomorphisms.PartB",
                                    "LayeredIsomorphisms.ThmBabOf","HeightAndVanishing.ThmHV",
                                    "CMFieldExponentialBounds.AdmissibleOfPageN")]
    names.append("Development.AutomorphicArithmetic.CharacterBoxes.PairGood")
    # leanchecker enumerates real files when discovering targets. Prior project
    # objects in the import build can be symlinks, so stage exact byte copies.
    inspected=work/"inspection"
    for name in names:
        rel=Path(*name.split(".")).with_suffix(".olean")
        destination=inspected/rel
        destination.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(work/"lib"/rel,destination)
    # Lean resolves each top-level package through a single library root.
    # Preserve that package layout for the remaining imports as well.
    for source in (work/"lib").rglob("*.olean"):
        dest=inspected/source.relative_to(work/"lib")
        if dest.exists():
            continue
        dest.parent.mkdir(parents=True,exist_ok=True)
        dest.symlink_to(source.resolve())
    env["LEAN_PATH"]=str(inspected)+os.pathsep+env["LEAN_PATH"]
    result={}
    for name in names:
        proc=subprocess.run([sdk/"bin/leanchecker","-v",name],cwd=work/"supplement",env=env,
                            text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,check=False)
        out=proc.stdout.strip()
        result[name]={"exit_code":proc.returncode,"message":out,"passed":proc.returncode==0 and out=="replaying "+name}
        print(name,result[name]["exit_code"],out[:450],file=sys.stderr,flush=True)
    print(json.dumps(result,indent=2))
    if not all(row["passed"] for row in result.values()):
        raise SystemExit(1)
if __name__=="__main__":
    main()
