"""Build the original arithmetic-to-centers path and replay selected original endpoints."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from graphlib import TopologicalSorter
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PRIOR = HERE.parent / "joint-witness"
sys.path.insert(0, str(PRIOR))
from build_original import FLAGS, PIN, ROOT, closure, dump, environment, pinned_tree, relative
import tomllib

PREFIX = "Development.AutomorphicArithmetic.AutomorphicVarieties."
TARGETS = tuple(PREFIX + suffix for suffix in (
    "QuadraticExtensions.IsAlgClosureRat",
    "QuadraticExtensions.LevelRk",
    "QuadraticExtensions.LevUAnti",
    "QuadraticExtensions.GenOfRk",
    "AdditiveValuationNorms.ABoundOfIsTower",
    "AdditiveValuationNorms.PadicUnitsDistanceLeMax",
    "LayeredIsomorphisms.Exc",
    "LayeredIsomorphisms.PartB",
))


def build(args):
    src, lib = args.work / "src", args.work / "lib"
    src.mkdir(parents=True, exist_ok=True)
    lib.mkdir(exist_ok=True)
    env, version = environment(args.toolchain, args.mathlib)
    env["LEAN_PATH"] = str(lib) + os.pathsep + env["LEAN_PATH"]
    tree = pinned_tree()
    config = tomllib.loads(subprocess.check_output(["git", "-C", str(ROOT), "show", PIN+":lakefile.toml"], text=True))
    settings = next(section for section in config["lean_lib"] if section["name"] == "GroundTheoryFields")
    prefixes = tuple(glob.removesuffix("+") for glob in settings["globs"])
    field_flag = "-DsynthInstance.maxHeartbeats=" + str(settings["leanOptions"]["synthInstance"]["maxHeartbeats"])
    graph = closure(TARGETS, args.source, tree, src)
    progress = args.work / "tower_progress.json"
    record = {"pin": PIN, "toolchain": version, "targets": TARGETS, "modules": {}, "replays": {},
              "flags": FLAGS, "additional_flags_by_prefix": {prefix:field_flag for prefix in prefixes}}
    prior_objects = []
    if args.cache:
        prior_objects.extend((PRIOR/"results"/file, args.cache / "lib")
                             for file in ("original_build.json", "bridge_build.json"))
    if progress.exists():
        prior_objects.append((progress, lib))
    for manifest, origin in prior_objects:
        saved = json.loads(manifest.read_bytes())
        if saved["pin"] != PIN or saved["toolchain"] != version:
            raise ValueError("Incompatible build record " + str(manifest))
        for name, entry in saved["modules"].items():
            if name not in graph:
                continue
            if name.startswith(prefixes) and saved.get("additional_flags_by_prefix") != record["additional_flags_by_prefix"]:
                continue
            path = relative(name, ".olean")
            obj = origin / path
            if (entry["source_blob"] != tree["src/" + relative(name, ".lean").as_posix()] or
                    sha256(obj.read_bytes()).hexdigest() != entry["olean_sha256"]):
                raise ValueError("Source or object differs for " + name)
            dest = lib / path
            if obj != dest:
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(obj, dest)
            record["modules"][name] = dict(source_blob=entry["source_blob"], olean_sha256=entry["olean_sha256"],
                                            origin=entry.get("origin", manifest.name))
    def compile_module(name):
        f = relative(name, ".lean")
        obj = lib / relative(name, ".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        extra = [field_flag] if name.startswith(prefixes) else []
        p = subprocess.run([args.toolchain/"bin/lean", *FLAGS, *extra, "--root=.", "-o", obj, f],
                           cwd=src, env=env, text=True, capture_output=True)
        if p.returncode or "declaration uses 'sorry'" in p.stdout + p.stderr:
            raise RuntimeError(name+"\n"+p.stdout+p.stderr)
        return dict(source_blob=tree["src/"+f.as_posix()], olean_sha256=sha256(obj.read_bytes()).hexdigest(),
                    origin="compiled")
    todo = graph.keys() - record["modules"].keys()
    order = TopologicalSorter({n:[p for p in graph[n] if p in todo] for n in todo})
    order.prepare()
    pending = {}
    print(f"{len(graph)} original modules, {len(todo)} to compile.", flush=True)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        while order.is_active():
            for n in order.get_ready():
                pending[pool.submit(compile_module,n)] = n
            finished, _ = wait(pending,return_when=FIRST_COMPLETED)
            for job in finished:
                n = pending.pop(job)
                record["modules"][n] = job.result()
                order.done(n)
            dump(progress, record)
    for name in TARGETS:
        p = subprocess.run([args.toolchain/"bin/leanchecker", "-v", name],
                           cwd=src,env=env,text=True,capture_output=True)
        log = (p.stdout+p.stderr).strip()
        if p.returncode or log != "replaying " + name:
            raise RuntimeError(name + "\n" + log)
        record["replays"][name] = log
    dump(args.out/"tower_build.json",record)
    print(f"Replayed {len(TARGETS)} original endpoints.")


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ("source","toolchain","mathlib","work","out","cache"):
        parser.add_argument("--"+name,type=lambda s: Path(s).resolve(),required=name!="cache")
    parser.add_argument("--workers",type=int,default=5)
    build(parser.parse_args())
