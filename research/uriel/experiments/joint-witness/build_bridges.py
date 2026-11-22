"""Extend the original build with the host, exception and family bridge modules."""
import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

from build_original import FLAGS, PIN, TARGETS, closure, dump, environment, pinned_tree, relative

EXTRA = tuple("Development.AutomorphicArithmetic."+name for name in (
    "CharacterBoxes.ZeroFreeAllOfTopG", "CharacterBoxes.DesWin",
    "AutomorphicVarieties.CMFieldExponentialBounds.AdmissibleOfPageN",
    "ShortNorms.supplyOfAdmOf", "AutomorphicVarieties.LayeredIsomorphisms.ThmBabOf",
    "ShortNorms.hostOfFieldOf")) + ("Formalism.SharpRestriction.DesignExistsOfChoices",)


def base_record(base, version, required, follow):
    path = base / "progress.json"
    try:
        info = json.loads(path.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        if follow:
            return {"modules": {}}
        raise ValueError(f"Missing or incomplete original-build record at {path}")
    if info["pin"] != PIN or info["toolchain"] != version or set(info["targets"]) != set(TARGETS):
        raise ValueError("Original-build source, toolchain or targets differ")
    if not follow and required - info["modules"].keys():
        raise ValueError("Original build is incomplete. Finish it first or specify --follow-base for a live build.")
    return info


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("source", "toolchain", "mathlib", "base", "work", "out"):
        parser.add_argument("--"+key, type=Path, required=True)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--follow-base", action="store_true", help="Read authenticated progress from a concurrent original build")
    args = parser.parse_args()
    tc, base, work = args.toolchain.resolve(), args.base.resolve(), args.work.resolve()
    src, lib = work/"src", work/"lib"
    work.mkdir(parents=True, exist_ok=False)
    lib.mkdir()
    tree = pinned_tree()
    graph = closure(EXTRA, args.source, tree, src)
    original = set(closure(TARGETS, args.source, tree)) & set(graph)
    env, version = environment(tc, args.mathlib.resolve())
    if not base.is_dir():
        raise ValueError(f"Original build directory does not exist: {base}")
    base_record(base, version, original, args.follow_base)
    env["LEAN_PATH"] = os.pathsep.join([str(lib), env["LEAN_PATH"]])
    record = dict(pin=PIN, toolchain=version, targets=list(EXTRA), modules={}, reused={}, replays={})
    pending = set(graph) - original
    complete = set()
    def worker(name):
        f = relative(name, ".lean")
        obj = lib/relative(name, ".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        proc = subprocess.run([tc/"bin/lean", *FLAGS, "--root=.", "-o", obj, f], cwd=src, env=env,
                              capture_output=True, text=True)
        log = proc.stdout+proc.stderr
        if proc.returncode or "declaration uses 'sorry'" in log:
            raise ValueError(name+"\n"+log)
        return dict(source_blob=tree["src/"+f.as_posix()], olean_sha256=sha256(obj.read_bytes()).hexdigest(),
                    warnings=log.count("warning:"))
    inflight = {}
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        while pending or inflight or original-complete:
            if original-complete:
                info = base_record(base, version, original, args.follow_base)
                for name in (original-complete) & info["modules"].keys():
                    row = info["modules"][name]
                    obj = base/"lib"/relative(name,".olean")
                    srcid = tree["src/"+relative(name, ".lean").as_posix()]
                    if row["source_blob"] != srcid or sha256(obj.read_bytes()).hexdigest() != row["olean_sha256"]:
                        raise RuntimeError("Cached module differs: "+name)
                    # Lean can resolve a package directory from a single search root.
                    # Keep all authenticated project objects under that same root.
                    dest = lib/relative(name,".olean")
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(obj, dest)
                    record["reused"][name] = row["olean_sha256"]
                    complete.add(name)
            ready = sorted(name for name in pending if all(dep in complete for dep in graph[name]))
            for name in ready[:max(0,args.workers-len(inflight))]:
                inflight[pool.submit(worker,name)] = name
                pending.remove(name)
            if not inflight:
                if pending and original<=complete:
                    raise RuntimeError("Unresolved project imports")
                if original-complete:
                    time.sleep(2)
                continue
            finished, _ = wait(inflight, timeout=1, return_when=FIRST_COMPLETED)
            for future in finished:
                name = inflight.pop(future)
                record["modules"][name] = future.result()
                complete.add(name)
            if finished:
                dump(work/"progress.json",record)
    for name in EXTRA:
        proc = subprocess.run([tc/"bin/leanchecker","-v",name],cwd=src,env=env,capture_output=True,text=True)
        log = (proc.stdout+proc.stderr).strip()
        if proc.returncode or log != "replaying "+name:
            raise RuntimeError(log)
        record["replays"][name] = dict(exit=proc.returncode,output=log)
    dump(args.out/"bridge_build.json",record)
    print(f"{len(record['modules'])} additional modules compiled. All {len(EXTRA)} endpoints replayed.")


if __name__ == "__main__":
    main()
