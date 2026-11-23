"""Compile the complete original project import closure and the new discriminant supplement."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from graphlib import TopologicalSorter
from hashlib import sha256
import json
import os
import re
from pathlib import Path
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("checkout", "original", "toolchain", "mathlib", "work"):
        parser.add_argument("--" + key, required=True, type=lambda p: Path(p).resolve())
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()
    sys.path.insert(0, str(args.checkout / "research/uriel/experiments/joint-witness"))
    from build_original import FLAGS, PIN, closure, environment, pinned_tree, relative

    root = "Formalism.SizeWindowBrackets.ChainSlopeWindows.DiscriminantSettingSatisfied"
    env, version = environment(args.toolchain, args.mathlib)
    args.work.mkdir(parents=True, exist_ok=False)
    source, objects = args.work / "src", args.work / "lib"
    objects.mkdir()
    tree = pinned_tree()
    graph = closure([root], args.original, tree, source)
    env["LEAN_PATH"] = str(objects) + os.pathsep + env["LEAN_PATH"]
    lean, kernel = (args.toolchain / "bin" / exe for exe in ("lean", "leanchecker"))

    def run(command):
        proc = subprocess.run(command, cwd=source, env=env, capture_output=True, text=True)
        log = (proc.stdout + proc.stderr).strip()
        if proc.returncode or "declaration uses 'sorry'" in log:
            raise RuntimeError(log)
        return log

    def compile_module(name):
        dest = objects / relative(name, ".olean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        log = run([lean, *FLAGS, "--root=.", "-o", dest, relative(name, ".lean")])
        return log, sha256(dest.read_bytes()).hexdigest()

    inventory = {}
    sorter = TopologicalSorter(graph)
    sorter.prepare()
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        while sorter.is_active():
            ready = list(sorter.get_ready())
            for name, (log, digest) in zip(ready, pool.map(compile_module, ready)):
                blob = tree["src/" + relative(name, ".lean").as_posix()]
                inventory[name] = {"source_git_blob": blob, "olean_sha256": digest}
                print(f"Compiled {name}", file=sys.stderr, flush=True)
                sorter.done(name)
    module = "DiscriminantOrbitLoss"
    supplement = Path(__file__).with_name(module + ".lean").read_bytes()
    (source / (module + ".lean")).write_bytes(supplement)
    axiom_log, digest = compile_module(module)
    axiom_lines = re.sub(r"\n +", " ", axiom_log).splitlines()
    expected = {"ten_surviving_bounds", "joint_zero_mass", "served_omission_zero",
                "normalized_omission", "joint_weighted_mass", "high_prime_floor"}
    prefix = "'Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.OrbitAudit."
    suffix = "' depends on axioms: [propext, Classical.choice, Quot.sound]"
    if set(axiom_lines) != {prefix + name + suffix for name in expected}:
        raise RuntimeError(axiom_log)
    checks = {}
    for name in (root, module):
        checks[name] = run([kernel, "-v", name])
        if checks[name] != "replaying " + name:
            raise RuntimeError(checks[name])
    record = {"pin": PIN, "flags": FLAGS, "toolchain": version, "root_original_module": root,
              "original_module_count": len(inventory), "original_modules": inventory, "kernel_replays": checks,
              "supplement": module, "supplement_sha256": sha256(supplement).hexdigest(),
              "supplement_olean_sha256": digest, "axioms": axiom_lines}
    print(json.dumps(record, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
