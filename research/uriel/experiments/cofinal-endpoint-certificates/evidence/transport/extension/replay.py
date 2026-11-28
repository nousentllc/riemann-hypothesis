"""Check the original field cap, principal observable, squared supply and marked host theorem."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode=True
from derive import render

ORIGINAL_FLAGS = ["--tstack=400000", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
                  "-DmaxSynthPendingDepth=3", "-Dpp.unicode.fun=true", "-DmaxHeartbeats=4000000"]
HERE=Path(__file__).resolve().parent
MATHLIB="0df444a360eaa60ab8c11dca51a86af692955474"
NAMES={
    "MarkedWindows": ("localDatum","rawSupply","widthRoom","winPairsBelowTwo","markedComparison"),
    "CapField": ("fieldChiWithCap",),
    "UnitCases": ("principalCap","principalLevel","winPairsUnit","winsFor","MarkedHost.forget"),
    "MarkedSupply": ("supplyWithSupport",),
    "HostInputs": ("hostFromInputs",),
    "LevelWindows": ("ofTied","ofCharacter","twoEndpoints"),
    "ScalarFromInputs": ("scalarBelowTwo","principalScalar"),
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def replay(sdk, mathlib, source, caches):
    sdk,mathlib,source=map(lambda p:Path(p).resolve(),(sdk,mathlib,source))
    caches=[Path(c).resolve() for c in caches]
    rev=subprocess.check_output(["git","-C",str(mathlib),"rev-parse","HEAD"],text=True).strip()
    if rev!=MATHLIB:
        raise ValueError("Mathlib revision mismatch")
    pins=json.loads((HERE/"input_pins.json").read_text())
    with tempfile.TemporaryDirectory() as temp:
        work=Path(temp)
        libs=[work,mathlib/".lake/build/lib/lean",*sorted((mathlib/".lake/packages").glob("*/.lake/build/lib/lean")),sdk/"lib/lean"]
        env={**os.environ,"LEAN_SYSROOT":str(sdk),"LEAN_PATH":os.pathsep.join(map(str,libs)),"PATH":str(sdk/"bin")+os.pathsep+os.environ["PATH"]}
        def run(cmd):
            result=subprocess.run([str(sdk/"bin"/cmd[0]),*cmd[1:]],cwd=work,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            if result.returncode:
                raise RuntimeError(result.stdout)
            return result.stdout.strip()
        version=run(["lean","--version"])
        if not version.startswith("Lean (version 4.33.1,"):
            raise ValueError(version)
        graph={}
        missing=set()
        for name,pin in pins.items():
            rel=Path(*name.split("."))
            src=source/"src"/rel.with_suffix(".lean")
            data=src.read_bytes()
            if hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()!=pin["source_blob"]:
                raise ValueError(name)
            graph[name]=[l[7:].strip() for l in data.decode().splitlines() if l.startswith("import ") and l[7:].strip() in pins]
            target=work/rel.with_suffix(".olean")
            target.parent.mkdir(parents=True,exist_ok=True)
            if caches:
                path=next((c/rel.with_suffix(".olean") for c in caches if (c/rel.with_suffix(".olean")).is_file() and digest(c/rel.with_suffix(".olean"))==pin["olean_sha256"]),None)
                if path is None:
                    missing.add(name)
                    shutil.copyfile(src,work/rel.with_suffix(".lean"))
                else:
                    target.symlink_to(path)
            else:
                missing.add(name)
                shutil.copyfile(src,work/rel.with_suffix(".lean"))
        if missing:
            built=set()
            def build(name):
                if name in built or name not in missing:
                    return
                for dep in graph[name]:
                    build(dep)
                rel=name.replace(".","/")
                run(["lean",*ORIGINAL_FLAGS,"--root=.","-o",rel+".olean",rel+".lean"])
                built.add(name)
            for name in graph:
                build(name)
        rendered = render(source)
        for name, text in rendered.items():
            if (HERE/name).read_text() != text:
                raise ValueError("Bundled source differs from its pinned-source derivation: "+name)
        sources={"MarkedWindows.lean":(HERE.parent/"MarkedWindows.lean").read_text(),
                 "LevelWindows.lean":(HERE.parent.parent/"level"/"LevelWindows.lean").read_text(),
                 **rendered,**{k:(HERE/k).read_text() for k in ("UnitCases.lean","HostInputs.lean","ScalarFromInputs.lean")}}
        declarations={}
        warnings={}
        messages=[]
        for name,names in NAMES.items():
            path=work/(name+".lean")
            path.write_text(sources[path.name])
            output=run(["lean","--root=.","-o",name+".olean",path.name])
            namespace = "FixedLevelWindows" if name == "LevelWindows" else "MarkedWindows"
            wanted=["'"+namespace+"."+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names]
            lines=output.splitlines()
            reported=[line for line in lines if line.startswith("'") and "depends on axioms:" in line]
            if reported!=wanted or "sorryAx" in output:
                raise ValueError(output)
            warnings[name]=[line for line in lines if ": warning:" in line]
            declarations.update({n:row for n,row in zip(names,wanted)})
            msg=run(["leanchecker","-v",name])
            if msg!="replaying "+name:
                raise ValueError(msg)
            messages.append(msg)
        return {"version":version,"mathlib_commit":rev,"input_mode":("authenticated cache" if not missing else "rebuild of pinned source closure" if not caches else "authenticated cache plus pinned-source rebuild"),
                "source_modules_rebuilt":len(missing),
                "pinned_sources":len(pins),"module_sha256":{k:hashlib.sha256(v.encode()).hexdigest() for k,v in sources.items()},
                "axioms":declarations,"source_warnings":warnings,"kernel":messages,"scope":"Original types and source-derived host construction, conditional on ShortNorm, SmallOne and VWinAt for the chosen character. Does not identify the marked support of the final global design."}


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    for arg in ("toolchain","mathlib","source"):
        ap.add_argument("--"+arg,type=Path,required=True)
    ap.add_argument("--objects",type=Path,action="append",default=[],help="repeat for authenticated object roots; missing or different objects are rebuilt from pinned source")
    opts=ap.parse_args()
    print(json.dumps(replay(opts.toolchain,opts.mathlib,opts.source,opts.objects),indent=2))
