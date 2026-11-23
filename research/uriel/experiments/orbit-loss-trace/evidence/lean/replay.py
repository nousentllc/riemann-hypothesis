"""Authenticate the retained-host library and replay the orbit-loss supplement."""
import argparse
from graphlib import TopologicalSorter
from hashlib import sha256
import json
import os
import re
from shutil import copyfile
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

TARGET = "Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.LatticeChainSuccOfPartial"
SUPPLEMENT = "OrbitLoss"
NAMES = [
    "orbitLoss_BTT_zero", "orbitLoss_E1_difference", "orbitLoss_relative",
    "orbitLoss_low", "orbitLoss_global", "orbitLoss_compare",
]


def digest(data):
    return sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("checkout", "original", "toolchain", "mathlib", "library"):
        parser.add_argument("--" + name, type=lambda s: Path(s).resolve(), required=True)
    parser.add_argument("--manifest", type=Path,
                        help="The verification record of your public retained-host replay")
    parser.add_argument("--original-object-manifest", type=Path,
                        help="Optional published sha256sum file for original project objects")
    parser.add_argument("--staged-originals", type=lambda s: Path(s).resolve(),
                        help="Verify fresh build objects from a separate compile of these seven sources; "
                             "requires their matching source files and replays each through leanchecker")
    args = parser.parse_args()
    experiments = args.checkout / "research/uriel/experiments"
    sys.path.insert(0, str(experiments / "joint-witness"))
    from build_original import FLAGS, PIN, closure, environment, pinned_tree, relative

    record_path = args.manifest or experiments / "retained-host/results/verification.json"
    record = json.loads(record_path.read_bytes())
    env, version = environment(args.toolchain, args.mathlib)
    if (record["pin"], record["flags"], record["toolchain"]) != (PIN, FLAGS, version):
        raise ValueError("Toolchain or retained-host record mismatch.")
    tree = pinned_tree()
    orig = record["source_closure"]
    inventory = {}
    for name in closure(orig["direct_original_imports"], args.original, tree):
        blob = tree["src/" + relative(name, ".lean").as_posix()]
        obj = args.library / relative(name, ".olean")
        inventory[name] = [blob, digest(obj.read_bytes())]
    data = (json.dumps(inventory, sort_keys=True, indent=2) + "\n").encode()
    signature = digest(data)
    if signature != orig["source_blob_and_object_inventory_sha256"]:
        raise ValueError("Imported module inventory mismatch.")
    graph = closure([TARGET], args.original, tree)
    published = {}
    if args.original_object_manifest:
        for row in args.original_object_manifest.read_text().splitlines():
            value, name = row.split(maxsplit=1)
            published[name.removeprefix("./")] = value
    with TemporaryDirectory() as scratch:
        work = Path(scratch)
        env["LEAN_PATH"] = str(work) + os.pathsep + env["LEAN_PATH"]
        rebuilt = {}
        def run(cmd):
            proc = subprocess.run(cmd, cwd=work, env=env, capture_output=True, text=True)
            log = (proc.stdout + proc.stderr).strip()
            if proc.returncode or "declaration uses 'sorry'" in log:
                raise RuntimeError(log)
            return log

        lean = args.toolchain / "bin/lean"
        kernel = args.toolchain / "bin/leanchecker"
        for name in TopologicalSorter(graph).static_order():
            f = relative(name, ".lean")
            obj = relative(name, ".olean")
            (work/obj).parent.mkdir(parents=True, exist_ok=True)
            if name in inventory:
                (work/obj).symlink_to(args.library/obj)
            else:
                (work/f).write_bytes((args.original/"src"/f).read_bytes())
                if args.staged_originals:
                    staged = args.staged_originals
                    if (staged/f).read_bytes() != (work/f).read_bytes():
                        raise ValueError(f"Staged source mismatch: {name}")
                    copyfile(staged/obj, work/obj)
                else:
                    run([lean, *FLAGS, "--root=.", "-o", obj, f])
                output = run([kernel, "-v", name])
                if output != "replaying " + name:
                    raise ValueError(output)
                entry = dict(git_blob=tree["src/" + f.as_posix()],
                             olean_sha256=digest((work/obj).read_bytes()))
                if published:
                    entry["published_olean_sha256"] = published[obj.as_posix()]
                    entry["matches_published_object"] = entry["olean_sha256"] == published[obj.as_posix()]
                entry["kernel_replay"] = output
                rebuilt[name] = entry
        replayed = rebuilt[TARGET]["kernel_replay"] if TARGET in rebuilt else run([kernel, "-v", TARGET])
        source = Path(__file__).with_name(SUPPLEMENT + ".lean").read_bytes()
        f = SUPPLEMENT + ".lean"
        (work/f).write_bytes(source)
        elaboration = run([lean, *FLAGS, "--root=.", "-o", SUPPLEMENT + ".olean", f])
        kernel_log = run([kernel, "-v", SUPPLEMENT])
        standard = "depends on axioms: [propext, Classical.choice, Quot.sound]"
        expected = {f"'Formalism.MainNotions.AuxBlock8.Pf.G5.{n}' {standard}" for n in NAMES}
        axiom_lines = re.sub(r"\n[ \t]+", " ", elaboration).splitlines()
        if set(axiom_lines) != expected or len(axiom_lines) != len(NAMES) or kernel_log != "replaying " + SUPPLEMENT:
            raise ValueError("Unexpected compiler/kernel output:\n" + elaboration + "\n" + kernel_log)
        print(json.dumps(dict(original_pin=PIN, lean=version["lean"], module=SUPPLEMENT,
                              supplement_sha256=digest(source), imported_inventory_checked=len(inventory),
                              inventory_sha256=signature, original_closure=len(graph),
                              original_modules_reused=len(graph)-len(rebuilt),
                              original_modules_rebuilt=rebuilt, original_endpoint_replay=replayed,
                              elaboration=axiom_lines, supplement_replay=kernel_log), indent=2))


if __name__ == "__main__":
    main()
