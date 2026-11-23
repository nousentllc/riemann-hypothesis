"""Compile and independently kernel-check the dropped-prime estimates (Python 3.9+)."""
import argparse
from graphlib import TopologicalSorter
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryDirectory

ROOT_MODULE = "Formalism.SizeWindowBrackets.ChainSlopeWindows.DiscriminantSettingSatisfied"
MODULE = "DroppedPrimeCosts"
PRIOR_RECEIPT = "4e20e8e1aff4d37c42ea8c0abf21a0ad186168cc1cfba244780c7da8041c0994"
NAMES = ["first_reciprocal_budget", "second_reciprocal_budget", "dropped_log_budget", "combined_budget"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("checkout", "original", "toolchain", "mathlib"):
        parser.add_argument("--" + key, type=Path, required=True)
    parser.add_argument("--cache", type=Path, help="Optional original project .olean directory")
    parser.add_argument("--prior-receipt", type=Path, help="Previous discriminant replay receipt")
    args = parser.parse_args()
    if bool(args.cache) != bool(args.prior_receipt):
        parser.error("--cache and --prior-receipt must be supplied together")
    sys.path.insert(0, str(args.checkout.resolve() / "research/uriel/experiments/joint-witness"))
    from build_original import FLAGS, PIN, closure, environment, pinned_tree, relative

    tc = args.toolchain.resolve()
    env, version = environment(tc, args.mathlib.resolve())
    src_file = Path(__file__).resolve().with_name(MODULE + ".lean")
    tool, checker = tc / "bin/lean", tc / "bin/leanchecker"
    tree = pinned_tree()
    with TemporaryDirectory(prefix="served-prime-drop-") as name:
        work = Path(name)
        src, obj = work / "src", work / "lib"
        obj.mkdir()
        graph = closure([ROOT_MODULE], args.original.resolve(), tree, src)
        paths = [str(obj)]
        prior = {}
        if args.cache:
            data = args.prior_receipt.read_bytes()
            if sha256(data).hexdigest() != PRIOR_RECEIPT:
                raise ValueError("Prior receipt identity differs")
            prior = json.loads(data)["original_modules"]
            if set(prior) != set(graph):
                raise ValueError("Original source closure differs")
            paths.append(str(args.cache.resolve()))
        env["LEAN_PATH"] = os.pathsep.join(paths + [env["LEAN_PATH"]])

        def run(command):
            proc = subprocess.run(command, env=env, cwd=src, text=True, capture_output=True)
            log = (proc.stdout + proc.stderr).strip()
            if proc.returncode or "declaration uses 'sorry'" in log:
                raise ValueError(log)
            return log

        def compile_one(module):
            o = obj / relative(module, ".olean")
            o.parent.mkdir(parents=True, exist_ok=True)
            log = run([tool, *FLAGS, "--root=.", "-o", o, relative(module, ".lean")])
            return log, sha256(o.read_bytes()).hexdigest()

        inventory = {}
        for module in TopologicalSorter(graph).static_order():
            blob = tree["src/" + relative(module, ".lean").as_posix()]
            if args.cache:
                full = args.cache / relative(module, ".olean")
                digest = sha256(full.read_bytes()).hexdigest()
                if {"source_git_blob": blob, "olean_sha256": digest} != prior[module]:
                    raise ValueError(f"Source or object mismatch at {module}")
            else:
                _, digest = compile_one(module)
            inventory[module] = {"source_git_blob": blob, "olean_sha256": digest}
        (src / src_file.name).write_bytes(src_file.read_bytes())
        log, object_digest = compile_one(MODULE)
        lines = re.sub(r"\n[ \t]+", " ", log).splitlines()
        expected = {("'Formalism.LFunctionChainParameters.SmallOrderPrimeLosses."
                     f"ServedPrimes.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]") for n in NAMES}
        if set(lines) != expected or len(lines) != len(expected):
            raise ValueError(log)
        kernels = {m: run([checker, "-v", m]) for m in (ROOT_MODULE, MODULE)}
        if any(text != f"replaying {m}" for m, text in kernels.items()):
            raise ValueError(kernels)
        result = {"pin": PIN, "module": MODULE, "toolchain": version, "flags": FLAGS,
                  "original_import": ROOT_MODULE, "original_project_modules": len(inventory),
                  "original_mode": "verified cached objects" if prior else "rebuilt",
                  "originals": inventory, "axioms": lines, "kernel": kernels,
                  "source_sha256": sha256(src_file.read_bytes()).hexdigest(),
                  "olean_sha256": object_digest}
        if prior:
            result["prior_receipt_sha256"] = PRIOR_RECEIPT
        print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
