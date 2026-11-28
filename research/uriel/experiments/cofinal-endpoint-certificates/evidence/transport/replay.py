"""Replay the modified WinPairs against original project declarations and the fixed-level comparison."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ORIGINAL_FLAGS = ["--tstack=400000", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
                  "-DmaxSynthPendingDepth=3", "-Dpp.unicode.fun=true", "-DmaxHeartbeats=4000000"]
HERE = Path(__file__).resolve().parent
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
MODS = ["Development.AutomorphicArithmetic.CharacterBoxes.PairGood",
        "Development.AutomorphicArithmetic.CharacterBoxes.TwistForm"]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def replay(sdk, mathlib, objects, source):
    sdk, mathlib, source = [Path(p).resolve() for p in (sdk, mathlib, source)]
    objects = Path(objects).resolve() if objects else None
    rev = subprocess.check_output(["git", "-C", str(mathlib), "rev-parse", "HEAD"], text=True).strip()
    if rev != PIN:
        raise ValueError("Mathlib commit mismatch")
    expected = json.loads((HERE / "inputs.json").read_text())
    for rel, blob in expected["source_blobs"].items():
        data = (source/"src"/rel).read_bytes()
        if hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest() != blob:
            raise ValueError(rel)
    for rel, h in (expected["objects"].items() if objects else ()):
        if digest(objects / rel) != h:
            raise ValueError(rel)
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        for rel in (expected["objects"] if objects else ()):
            dest = work / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.symlink_to(objects / rel)
        lib = [work, *([objects] if objects else []), mathlib/".lake/build/lib/lean", *sorted((mathlib/".lake/packages").glob("*/.lake/build/lib/lean")), sdk/"lib/lean"]
        env = {**os.environ, "LEAN_SYSROOT": str(sdk), "LEAN_PATH": os.pathsep.join(map(str,lib)), "PATH": str(sdk/"bin")+os.pathsep+os.environ["PATH"]}
        def run(cmd):
            p = subprocess.run([str(sdk/"bin"/cmd[0]), *cmd[1:]], cwd=work, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if p.returncode:
                raise RuntimeError(p.stdout)
            return p.stdout.strip()
        version = run(["lean", "--version"])
        if not version.startswith("Lean (version 4.33.1,"):
            raise ValueError(version)
        if not objects:
            built = set()
            def compile_pinned(rel):
                if rel in built:
                    return
                path = source/"src"/rel
                for line in path.read_text().splitlines():
                    if line.startswith("import "):
                        dep = line[7:].strip().replace(".", "/")+".lean"
                        if dep in expected["source_blobs"]:
                            compile_pinned(dep)
                target = work/rel
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(path,target)
                run(["lean",*ORIGINAL_FLAGS,"--root=.","-o",str(Path(rel).with_suffix(".olean")),rel])
                built.add(rel)
            for rel in expected["source_blobs"]:
                compile_pinned(rel)
        for mod in MODS:
            lean = Path(*mod.split(".")).with_suffix(".lean")
            path = source/"src"/lean
            if digest(path) != expected["sources"][str(lean)]:
                raise ValueError(str(lean))
            (work/lean).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, work/lean)
            run(["lean","--root=.", "-o", str(lean.with_suffix(".olean")), str(lean)])
        shutil.copyfile(HERE/"MarkedWindows.lean",work/"MarkedWindows.lean")
        output=run(["lean","--root=.","-o","MarkedWindows.olean","MarkedWindows.lean"])
        checks = [run(["leanchecker","-v",name]) for name in [*MODS,"MarkedWindows"]]
        decls = ["localDatum", "rawSupply", "widthRoom", "winPairsBelowTwo", "markedComparison"]
        required = ["'MarkedWindows."+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in decls]
        if checks != ["replaying "+name for name in [*MODS,"MarkedWindows"]] or output.splitlines() != required:
            raise ValueError((checks,output))
        return {"version":version,"mathlib_commit":rev,"tracked_original_objects":len(expected["objects"]), "input_mode":"authenticated cache" if objects else "rebuild of pinned source closure", "source_sha256":digest(HERE/"MarkedWindows.lean"), "axioms":output.splitlines(),"kernel":checks,"scope":"Two original intermediate modules and the supplementary declarations. The host/design/TopG reconstruction is a written audit, and no full build was run."}


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--objects", type=Path, help="optional authenticated original object cache; omit to rebuild 408 source modules")
    for arg in ("toolchain", "mathlib", "source"):
        ap.add_argument("--"+arg, required=True, type=Path)
    args=ap.parse_args()
    print(json.dumps(replay(args.toolchain,args.mathlib,args.objects,args.source),indent=2))
