"""Check the common-pair strengthening against the actual pinned WinPairs module."""
import argparse
from graphlib import TopologicalSorter
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess

from build_original import HERE, PIN, FLAGS, closure, dump, environment, pinned_tree, relative

WIN = "Development.AutomorphicArithmetic.CharacterBoxes.WinPairs"
NEW_MODULE = "FixedPair"
FRESH = {WIN, "Development.AutomorphicArithmetic.CharacterBoxes.PairGood",
         "Development.AutomorphicArithmetic.CharacterBoxes.TwistForm"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("source", "toolchain", "mathlib", "work", "out"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--reuse", type=Path, help="Reuse hash-verified objects from build_original.py")
    args = parser.parse_args()
    work, source = args.work.resolve(), args.source.resolve()
    work.mkdir(parents=True, exist_ok=False)
    src, lib = work / "src", work / "lib"
    tree = pinned_tree()
    graph = closure([WIN], source, tree, src)
    tc = args.toolchain.resolve()
    env, version = environment(tc, args.mathlib.resolve())
    env["LEAN_PATH"] = str(lib) + os.pathsep + env["LEAN_PATH"]
    report = dict(pin=PIN, toolchain=version, original_closure=len(graph), modules={}, replays={})
    cached = {}
    if args.reuse:
        provenance = json.loads((args.reuse / "progress.json").read_text())
        if provenance["pin"] != PIN or provenance["toolchain"] != version:
            raise ValueError("Original build provenance differs")
        cached = provenance["modules"]

    def execute(command):
        process = subprocess.run(command, env=env, cwd=src, text=True,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if process.returncode or "declaration uses 'sorry'" in process.stdout:
            raise RuntimeError(f"{command[-1]}\n{process.stdout}")
        return process.stdout

    def compile_one(name, dest):
        return execute([tc / "bin/lean", *FLAGS, "--root=.", "-o", dest, relative(name, ".lean")])

    def replay(name):
        output = execute([tc / "bin/leanchecker", "-v", name]).strip()
        if output != f"replaying {name}":
            raise ValueError(output)
        report["replays"][name] = dict(exit=0, output=output)

    for mod in TopologicalSorter(graph).static_order():
        rel = relative(mod, ".olean")
        dest = lib / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        source_oid = tree["src/" + relative(mod, ".lean").as_posix()]
        if mod in cached and mod not in FRESH:
            inputs = cached[mod]
            obj = args.reuse / "lib" / rel
            if inputs["source_blob"] != source_oid or sha256(obj.read_bytes()).hexdigest() != inputs["olean_sha256"]:
                raise ValueError(f"Cached object differs at {mod}")
            shutil.copyfile(obj, dest)
            mode = "authenticated original build"
            output = ""
        else:
            output = compile_one(mod, dest)
            mode = "fresh compilation"
        report["modules"][mod] = dict(source_blob=source_oid, olean_sha256=sha256(dest.read_bytes()).hexdigest(),
                                      mode=mode, output=output.strip())
        print(f"{mode}: {mod}", flush=True)
    replay(WIN)
    file = HERE / f"{NEW_MODULE}.lean"
    shutil.copyfile(file, src / file.name)
    dest = lib / f"{NEW_MODULE}.olean"
    log = compile_one(NEW_MODULE, dest)
    if "Checked direct proof dependencies for strengthening and weakening" not in log:
        raise ValueError("The proof dependency control did not run")
    for decl in ("winPairs_fixed", "pointwise_of_fixed", "two_rows"):
        if f"UrielJoint.{decl}" not in log:
            raise ValueError(f"Axiom output missing for {decl}")
    replay(NEW_MODULE)
    report["extension"] = dict(module=NEW_MODULE, source_sha256=sha256(file.read_bytes()).hexdigest(),
                               olean_sha256=sha256(dest.read_bytes()).hexdigest(), compiler_output=log.strip())
    dump(args.out / "fixed_pair.json", report)
    print(log.strip())


if __name__ == "__main__":
    main()
