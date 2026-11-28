"""Build selected original modules and replay the endpoints in an isolated directory."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from graphlib import TopologicalSorter
from hashlib import sha1, sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "second"))
from formal import FLAGS, PIN, ROOT, dump, environment

WINDOW = "Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Window"
CORE = "Development.AutomorphicArithmetic.PrimitiveCosets.LevelGmLeOnFamilyScales"
COH = "Formalism.GaloisCohomology.Statement"
TARGETS = (WINDOW, CORE, COH)


def relative(module, suffix):
    return Path(*module.split(".")).with_suffix(suffix)


def pinned_tree():
    raw = subprocess.check_output(["git", "-C", str(ROOT), "ls-tree", "-r", "-z", PIN, "src"])
    entries = {}
    for entry in raw.rstrip(b"\0").split(b"\0"):
        header, path = entry.split(b"\t", 1)
        entries[path.decode()] = header.split()[2].decode()
    return entries


def pinned_source(path, archive, tree):
    data = (archive / path).read_bytes()
    oid = sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    if oid != tree[str(path)]:
        raise ValueError(f"Source differs from the pinned Git object at {path}")
    return data


def dependencies(module, archive, tree):
    path = Path("src") / relative(module, ".lean")
    data = pinned_source(path, archive, tree)
    imports = []
    for line in re.findall(rb"(?m)^import[ \t]+([^\n]+)", data):
        for dep in line.split(b"--")[0].decode().split():
            if str(Path("src") / relative(dep, ".lean")) in tree:
                imports.append(dep)
            elif dep.split(".")[0] not in {"Mathlib", "Lean", "Std", "Init"}:
                raise ValueError(f"Unresolved {dep} in {module}")
    return data, imports


def closure(targets, archive, tree, dest=None):
    graph = {}
    todo = list(targets)
    while todo:
        module = todo.pop()
        if module in graph:
            continue
        data, imports = dependencies(module, archive, tree)
        graph[module] = imports
        todo.extend(imports)
        if dest is not None:
            out = dest / relative(module, ".lean")
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_bytes(data)
    return graph


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for name in ("source", "toolchain", "mathlib", "work", "out"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--workers", type=int, default=4)
    args = ap.parse_args()
    tc, lib, work = args.toolchain.resolve(), args.mathlib.resolve(), args.work.resolve()
    tree, src, obj = pinned_tree(), work / "src", work / "lib"
    work.mkdir(parents=True, exist_ok=False)
    obj.mkdir()
    graph = closure(TARGETS, args.source, tree, src)
    env, version = environment(tc, lib)
    env["LEAN_PATH"] = str(obj) + os.pathsep + env["LEAN_PATH"]
    args.out.mkdir(parents=True, exist_ok=True)
    spec = dict(pin=PIN, toolchain=version, targets=list(TARGETS), workers=args.workers,
                closure_counts={t:len(closure([t], args.source, tree)) for t in TARGETS},
                modules={}, replays={})
    def compile_module(name):
        f = relative(name, ".lean")
        dest = obj / relative(name, ".olean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        command = [tc/"bin/lean", *FLAGS, "--root=.", "-o", dest, f]
        proc = subprocess.run(command, cwd=src, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = proc.stdout.decode()
        if proc.returncode or "declaration uses 'sorry'" in log:
            raise RuntimeError(f"{name}\n{log}")
        return dict(source_blob=tree["src/"+f.as_posix()], olean_sha256=sha256(dest.read_bytes()).hexdigest(),
                    warnings=log.count("warning:"))
    order = TopologicalSorter(graph)
    order.prepare()
    futures = {}
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        while order.is_active():
            for name in order.get_ready():
                futures[pool.submit(compile_module, name)] = name
            done, _ = wait(futures, return_when=FIRST_COMPLETED)
            for future in done:
                name = futures.pop(future)
                spec["modules"][name] = future.result()
                order.done(name)
            if len(spec["modules"]) % 10 == 0:
                print(f'{len(spec["modules"])} / {len(graph)} compiled', flush=True)
            dump(work/"progress.json", spec)
    for name in TARGETS:
        proc = subprocess.run([tc/"bin/leanchecker", "-v", name], cwd=src, env=env, capture_output=True, text=True)
        log = (proc.stdout+proc.stderr).strip()
        if proc.returncode or log != "replaying "+name:
            raise RuntimeError(log)
        spec["replays"][name] = dict(exit=proc.returncode, output=log)
    dump(args.out/"original_build.json", spec)
    print(f"{len(graph)} original modules compiled, {len(TARGETS)} endpoints replayed.")


if __name__ == "__main__":
    main()
