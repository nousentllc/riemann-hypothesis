"""Replay the served-prime theorems with pinned original sources and Lean."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from graphlib import TopologicalSorter
from hashlib import sha1, sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys

PIN = "40e56bab026552e089d7afcfeff08d2defb9c005"
LEAN = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
ROOT = "Formalism.SizeWindowBrackets.ChainSlopeWindows.DiscriminantSettingSatisfied"
MODULE = "ServedPrimeWeights"
FLAGS = ["-j1", "--tstack=400000", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
         "-DmaxSynthPendingDepth=3", "-Dpp.unicode.fun=true", "-DmaxHeartbeats=4000000"]


def run(cmd, cwd, env=None):
    result = subprocess.run(cmd, cwd=cwd, env=env, text=True, capture_output=True)
    log = (result.stdout + result.stderr).strip()
    if result.returncode or "declaration uses 'sorry'" in log:
        raise RuntimeError(f"{cmd}\n{log}")
    return log


def module_file(module, ext):
    return Path(*module.split(".")).with_suffix(ext)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("repo", "original", "toolchain", "mathlib", "work"):
        parser.add_argument("--" + name, type=lambda x: Path(x).resolve(), required=True)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--cache", type=lambda p: Path(p).resolve(), help="Verified original .olean directory")
    parser.add_argument("--prior-receipt", type=Path, help="Pinned prior discriminant replay JSON")
    args = parser.parse_args()
    if bool(args.cache) != bool(args.prior_receipt):
        parser.error("Supply --cache together with --prior-receipt")
    args.work.mkdir(exist_ok=False, parents=True)
    source, objects = args.work / "src", args.work / "lib"
    source.mkdir()
    objects.mkdir()
    env = dict(os.environ, LEAN_SYSROOT=str(args.toolchain),
               PATH=str(args.toolchain / "bin") + os.pathsep + os.environ["PATH"])
    lean, kernel, lake = (args.toolchain / "bin" / name for name in ("lean", "leanchecker", "lake"))
    if run([lean, "--githash"], args.work, env) != LEAN:
        raise ValueError("Lean revision differs from the pin")
    version = run([lean, "--version"], args.work, env)

    def source_at(path):
        data = (args.original / path).read_bytes()
        oid = sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        expected = run(["git", "rev-parse", PIN + ":" + path.as_posix()], args.repo)
        if oid != expected:
            raise ValueError(f"Original bytes differ from Git at {path}")
        return data, oid

    packages = {}
    manifest, _ = source_at(Path("lake-manifest.json"))
    for pkg in json.loads(manifest)["packages"]:
        repo = args.mathlib if pkg["name"] == "mathlib" else args.mathlib / ".lake/packages" / pkg["name"]
        rev = run(["git", "rev-parse", "HEAD"], repo)
        if rev != pkg["rev"] or run(["git", "status", "--porcelain", "--untracked-files=no"], repo):
            raise ValueError(f"Package mismatch: {pkg['name']}")
        packages[pkg["name"]] = rev
    path = run([lake, "env", "printenv", "LEAN_PATH"], args.mathlib, env)
    env["LEAN_PATH"] = str(objects) + os.pathsep + path
    if args.cache:
        env["LEAN_PATH"] = os.pathsep.join([str(objects), str(args.cache), path])
    graph, inventory = {}, {}
    pending = [ROOT]
    while pending:
        module = pending.pop()
        if module in graph:
            continue
        filename = module_file(module, ".lean")
        data, oid = source_at(Path("src") / filename)
        target = source / filename
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        imports = []
        for row in re.findall(rb"(?m)^import[ \t]+([^\n]+)", data):
            for imp in row.split(b"--")[0].decode().split():
                if (args.original / "src" / module_file(imp, ".lean")).is_file():
                    imports.append(imp)
                elif imp.split(".")[0] not in {"Mathlib", "Lean", "Init", "Std"}:
                    raise ValueError(f"Unresolved import {imp} from {module}")
        graph[module] = imports
        inventory[module] = {"source_git_blob": oid}
        pending.extend(imports)

    def compile_module(module):
        destination = objects / module_file(module, ".olean")
        destination.parent.mkdir(parents=True, exist_ok=True)
        log = run([lean, *FLAGS, "--root=.", "-o", destination, module_file(module, ".lean")], source, env)
        return log, sha256(destination.read_bytes()).hexdigest()

    if args.cache:
        data = args.prior_receipt.read_bytes()
        if sha256(data).hexdigest() != "4e20e8e1aff4d37c42ea8c0abf21a0ad186168cc1cfba244780c7da8041c0994":
            raise ValueError("Prior discriminant receipt differs")
        prior = json.loads(data)["original_modules"]
        if set(graph) != set(prior):
            raise ValueError("Cache closure differs")
        for module, row in inventory.items():
            obj = args.cache / module_file(module, ".olean")
            row["olean_sha256"] = sha256(obj.read_bytes()).hexdigest()
            if row != prior[module]:
                raise ValueError("Incorrect cached object or source: " + module)
    else:
        order = TopologicalSorter(graph)
        order.prepare()
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            while order.is_active():
                ready = order.get_ready()
                for module, (_, digest) in zip(ready, pool.map(compile_module, ready)):
                    inventory[module]["olean_sha256"] = digest
                    print("Compiled " + module, file=sys.stderr, flush=True)
                    order.done(module)

    location = Path(__file__).resolve().parent
    supplements = {}
    module_inputs = [
        (MODULE, "ServedWeights", location),
        ("DroppedPrimeCosts", "ServedPrimes", location.parent / "drop_lean"),
        ("ServedBandTransfer", "ServedBand", location),
    ]
    checks = {ROOT: run([kernel, "-v", ROOT], source, env)}
    for module, namespace, directory in module_inputs:
        addition = (directory / (module + ".lean")).read_bytes()
        (source / (module + ".lean")).write_bytes(addition)
        log, digest = compile_module(module)
        axioms = re.sub(r"\n[ \t]+", " ", log).splitlines()
        before = "'Formalism.LFunctionChainParameters.SmallOrderPrimeLosses." + namespace + "."
        after = "' depends on axioms: [propext, Classical.choice, Quot.sound]"
        names = re.findall(rb"(?m)^#print axioms (\w+)$", addition)
        if not names or set(axioms) != {before + n.decode() + after for n in names} or len(names) != len(axioms):
            raise ValueError("Axiom audit differed:\n" + log)
        checks[module] = run([kernel, "-v", module], source, env)
        supplements[module] = {"source_sha256": sha256(addition).hexdigest(),
                               "olean_sha256": digest, "axioms": axioms}
    if any(value != "replaying " + key for key, value in checks.items()):
        raise ValueError(f"Unexpected kernel output: {checks}")
    result = {"pin": PIN, "compiler": version, "lean_commit": LEAN, "flags": FLAGS, "packages": packages,
              "project_root": ROOT, "original_modules": inventory, "supplements": supplements,
              "source_of_original_objects": "verified cache" if args.cache else "new compilation",
              "kernel_replays": checks}
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
