"""Authenticate the imported sources, rebuild the supplements and replay their Lean declarations."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from graphlib import TopologicalSorter
from hashlib import sha1, sha256
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ORIGINAL = "40e56bab026552e089d7afcfeff08d2defb9c005"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
CORE = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
IMPORT = re.compile(r"^(?:public )?import\s+([\w.]+)", re.MULTILINE)
FLAGS = ["-j1", "--tstack=400000", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
         "-DmaxSynthPendingDepth=3", "-Dpp.unicode.fun=true", "-DmaxHeartbeats=4000000"]
UNITS = ["base", "ascent", "descent", "ranks", "roster", "numerics", "moving"]

def read(name):
    return json.loads((HERE/name).read_bytes())

def oid(data):
    return sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()

def prepare(source, git):
    pins = read("input_pins.json")
    prior = read("prior_sources.json")
    if read("prior_pins.json") != {n:{k:v for k,v in pins[n].items() if k!="object"} for n in prior}:
        raise ValueError("Earlier research manifest mismatch")
    new = {p.stem:p for unit in UNITS for p in (HERE/unit).glob("*.lean")}
    if set(pins) & set(new):
        raise ValueError("New module shadows pinned dependency")
    graph, sources = {}, {}
    def visit(n):
        if n in graph:
            return
        if n in new:
            content = new[n].read_bytes()
        elif n in prior:
            content = prior[n].encode()
        else:
            relative = Path(*n.split(".")).with_suffix(".lean")
            file = source/"src"/relative
            if not file.exists():
                if n in pins:
                    raise ValueError("Missing source "+str(file))
                return
            content = file.read_bytes()
        if n not in new and oid(content) != pins[n]["blob"]:
            raise ValueError("Source hash differs: "+n)
        sources[n] = content
        graph[n] = []
        for dep in IMPORT.findall(content.decode()):
            visit(dep)
            if dep in graph:
                graph[n].append(dep)
    for name in new:
        visit(name)
    if set(graph) != set(pins) | set(new):
        raise ValueError("Dependency closure differs from the manifest")
    if git:
        base = subprocess.check_output(["git","-c","core.quotepath=false","-C",git,
                                        "ls-tree","-r",ORIGINAL,"src"],text=True)
        trees = {p:head.split()[2] for head,p in (row.split("\t",1) for row in base.splitlines())}
        for n,pin in pins.items():
            if n in prior:
                value = subprocess.check_output(["git","-C",git,"rev-parse",pin["commit"]+":"+pin["path"]],text=True).strip()
            else:
                value = trees["src/"+n.replace(".","/")+".lean"]
            if value != pin["blob"]:
                raise ValueError("Git source mismatch: "+n)
    return pins, prior, new, graph, sources

def run(args):
    pins,prior,new,graph,sources = prepare(args.source,args.git)
    report = dict(original_commit=ORIGINAL, original_sources=len(pins)-len(prior),
                  prior_sources=len(prior), new_sources=len(new))
    if args.audit_only:
        report["git_verified"] = bool(args.git)
        return report
    sdk, mathlib = args.toolchain, args.mathlib
    if subprocess.check_output(["git","-C",mathlib,"rev-parse","HEAD"],text=True).strip() != MATHLIB:
        raise ValueError("Mathlib commit differs")
    version = subprocess.check_output([sdk/"bin/lean","--version"],text=True).strip()
    if "version 4.33.1," not in version or CORE not in version:
        raise ValueError(version)
    with tempfile.TemporaryDirectory(prefix="seven-slot-") as tmp:
        root = Path(tmp)
        libs = [root,mathlib/".lake/build/lib/lean",*sorted((mathlib/".lake/packages").glob("*/.lake/build/lib/lean")),sdk/"lib/lean"]
        env = dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,libs)),LEAN_SYSROOT=str(sdk),PATH=str(sdk/"bin")+os.pathsep+os.environ["PATH"])
        def command(cmd):
            result = subprocess.run([sdk/"bin"/cmd[0],*cmd[1:]],cwd=root,env=env,stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,text=True)
            if result.returncode or "declaration uses 'sorry'" in result.stdout:
                raise RuntimeError(str(cmd[-1])+"\n"+result.stdout)
            return result.stdout.strip()
        def build(n):
            rel = Path(*n.split(".")).with_suffix(".lean")
            target = (root/rel).with_suffix(".olean")
            target.parent.mkdir(parents=True,exist_ok=True)
            if n in pins:
                expected = pins[n].get("object")
                for library in args.objects:
                    cache = (library/rel).with_suffix(".olean")
                    if expected and cache.is_file() and sha256(cache.read_bytes()).hexdigest() == expected:
                        target.symlink_to(cache)
                        return n,"cached",None
            (root/rel).write_bytes(sources[n])
            log = command(["lean",*(FLAGS if n in pins and n not in prior else ["-j1"]),
                           "--root=.","-o",str(rel.with_suffix(".olean")),str(rel)])
            if n not in new:
                return n,"rebuilt",None
            outputs = [line for line in log.splitlines() if line.startswith("'") and "axiom" in line]
            names = re.findall(r"^#print axioms ([\w.]+)",sources[n].decode(),re.M)
            if len(names) != len(outputs) or not names:
                raise ValueError("Missing #print checks for "+n+"\n"+log)
            for name,line in zip(names,outputs):
                full_name = line.split("'")[1]
                if not (full_name == name or full_name.endswith("."+name)):
                    raise ValueError(line)
                axioms = re.search(r"depends on axioms: \[(.*?)\]$",line)
                if axioms:
                    if set(axioms.group(1).split(", ")) - {"propext","Classical.choice","Quot.sound"}:
                        raise ValueError(line)
                elif "does not depend on any axioms" not in line:
                    raise ValueError(line)
            check = command(["leanchecker","-v",n])
            if check != "replaying "+n:
                raise ValueError(check)
            return n,"new",dict(sha256=sha256(sources[n]).hexdigest(),kernel=check,axioms=outputs)
        order = TopologicalSorter(graph)
        order.prepare()
        counts = {"cached":0,"rebuilt":0,"new":0}
        modules = {}
        with ThreadPoolExecutor(args.workers) as pool:
            while order.is_active():
                ready = order.get_ready()
                for n,mode,receipt in pool.map(build,ready):
                    counts[mode] += 1
                    if receipt:
                        modules[n] = receipt
                order.done(*ready)
        report.update(version=version,mathlib=MATHLIB,inputs=counts,modules=dict(sorted(modules.items())),
                      declarations=sum(len(m["axioms"]) for m in modules.values()))
    return report

if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    for k in ("source","git","toolchain","mathlib"):
        ap.add_argument("--"+k,type=lambda x:Path(x).resolve(),required=(k=="source"))
    ap.add_argument("--objects",action="append",default=[],type=lambda x:Path(x).resolve(),
                    help="optional verified compiled-input root, repeatable")
    ap.add_argument("--workers",type=int,default=3)
    ap.add_argument("--audit-only",action="store_true")
    args = ap.parse_args()
    if not args.audit_only and not (args.toolchain and args.mathlib):
        ap.error("--toolchain and --mathlib are required for a kernel replay")
    print(json.dumps(run(args),indent=2,ensure_ascii=False))
