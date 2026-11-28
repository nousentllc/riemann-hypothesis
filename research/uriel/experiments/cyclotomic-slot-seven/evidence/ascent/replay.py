"""Build and kernel-replay the seven-class induction with source-pinned dependencies."""
import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
IMPORTS = re.compile(r"^(?:public )?import\s+([\w.]+)", re.M)
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
ORIGINAL = "40e56bab026552e089d7afcfeff08d2defb9c005"
FLAGS = ["--tstack=400000", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
         "-DmaxSynthPendingDepth=3", "-Dpp.unicode.fun=true", "-DmaxHeartbeats=4000000"]


def blob(data):
    return hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()


def replay(source, sdk, mathlib, caches):
    pins = json.loads((HERE/"imports.json").read_text())
    prior = json.loads((HERE/"prior_sources.json").read_text())
    refs = {Path(row["path"]).stem:row for row in json.loads((HERE/"source_map.json").read_text())}
    modules = {name: HERE/(name+".lean") for name in
               ["SevenTransport","SevenRamification","SevenCover","SevenClassStep","SevenInertia","SevenAscent"]}
    modules["SevenBase"] = HERE.parent/"base/SevenBase.lean"
    rev = subprocess.check_output(["git","-C",mathlib,"rev-parse","HEAD"],text=True).strip()
    if rev != MATHLIB:
        raise ValueError("Unexpected Mathlib revision")
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        libs = [work, mathlib/".lake/build/lib/lean", *sorted((mathlib/".lake/packages").glob("*/.lake/build/lib/lean")), sdk/"lib/lean"]
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str,libs)), LEAN_SYSROOT=str(sdk), PATH=str(sdk/"bin")+os.pathsep+os.environ["PATH"])
        def run(*cmd):
            r = subprocess.run([sdk/"bin"/cmd[0],*cmd[1:]],cwd=work,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            if r.returncode or "declaration uses 'sorry'" in r.stdout:
                raise RuntimeError(r.stdout)
            return r.stdout.strip()
        version = run("lean","--version")
        if not version.startswith("Lean (version 4.33.1,") or "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" not in version:
            raise ValueError(version)
        seen, fresh, checked = set(), [], {}
        def build(n):
            if n in seen:
                return
            path = Path(*n.split(".")).with_suffix(".lean")
            obj = (work/path).with_suffix(".olean")
            if n in modules:
                data = modules[n].read_bytes()
            elif n in prior:
                data = prior[n].encode()
                if blob(data)!=refs[n]["blob"]:
                    raise ValueError("Modified research import: "+n)
            elif n in pins:
                data = (source/"src"/path).read_bytes()
                if blob(data)!=pins[n][0]:
                    raise ValueError("Modified original source: "+n)
            else:
                if (source/"src"/path).exists():
                    raise ValueError("Unpinned project import: "+n)
                return
            for dep in IMPORTS.findall(data.decode()):
                build(dep)
            obj.parent.mkdir(parents=True,exist_ok=True)
            if n in pins:
                for root in caches:
                    cache=(root/path).with_suffix(".olean")
                    if cache.is_file() and hashlib.sha256(cache.read_bytes()).hexdigest()==pins[n][1]:
                        obj.symlink_to(cache)
                        seen.add(n)
                        return
                fresh.append(n)
            (work/path).write_bytes(data)
            printout=run("lean","-j1",*(FLAGS if n in pins else []),"--root=.","-o",str(path.with_suffix(".olean")),str(path))
            if n not in pins:
                axs=[line for line in printout.splitlines() if "depends on axioms:" in line]
                if not axs and n in modules or any(not a.endswith("[propext, Classical.choice, Quot.sound]") for a in axs):
                    raise ValueError(printout)
                result=run("leanchecker","-v",n)
                if result!="replaying "+n:
                    raise ValueError(result)
                checked[n]=dict(source_sha256=hashlib.sha256(data).hexdigest(),axioms=axs,kernel=result)
            seen.add(n)
        build("SevenAscent")
        if seen != set(modules) | set(prior) | set(pins):
            raise ValueError("Research import graph changed")
        return dict(original=ORIGINAL,mathlib=rev,lean=version,pinned_original_modules=len(pins),
                    original_modules_rebuilt=fresh,earlier_research_modules=sorted(prior),modules=checked)

if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    for key in ("source","toolchain","mathlib"):
        ap.add_argument("--"+key,type=Path,required=True)
    ap.add_argument("--objects",type=Path,action="append",default=[])
    a=ap.parse_args()
    print(json.dumps(replay(a.source.resolve(),a.toolchain.resolve(),a.mathlib.resolve(),
                            [c.resolve() for c in a.objects]),indent=2))
