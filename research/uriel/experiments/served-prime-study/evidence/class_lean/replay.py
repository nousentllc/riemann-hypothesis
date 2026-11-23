"""Authenticate cached original modules and kernel-replay the boxed character estimate."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryDirectory


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("checkout", "original", "toolchain", "mathlib", "library", "manifest"):
        parser.add_argument("--" + key, type=lambda arg: Path(arg).resolve(), required=True)
    parser.add_argument("--representatives", action="store_true",
                        help="replay the separate construction of the three primitive representatives")
    args = parser.parse_args()
    sys.path.insert(0, str(args.checkout / "research/uriel/experiments/joint-witness"))
    from build_original import FLAGS, PIN, closure, environment, pinned_tree, relative
    env, version = environment(args.toolchain, args.mathlib)
    record = json.loads(args.manifest.read_bytes())
    retained_pin = "9ac7e1b546b132edde02709e1c0af1bfccd40755"
    manifest_path = "research/uriel/experiments/retained-host/results/verification.json"
    canonical = json.loads(subprocess.check_output(
        ["git", "-C", str(args.checkout), "show", retained_pin + ":" + manifest_path]))
    if (record["pin"], record["flags"], record["toolchain"]) != (PIN, FLAGS, version):
        raise RuntimeError("Toolchain and retained-host inventory differ.")
    src_closure = record["source_closure"]
    if src_closure["direct_original_imports"] != canonical["source_closure"]["direct_original_imports"]:
        raise RuntimeError("The original import roots differ from the pinned retained-host run.")
    if canonical["toolchain"] == version and (src_closure["source_blob_and_object_inventory_sha256"]
            != canonical["source_closure"]["source_blob_and_object_inventory_sha256"]):
        raise RuntimeError("The object inventory differs from the record for this toolchain.")
    tree = pinned_tree()
    inventory = {}
    for name in closure(src_closure["direct_original_imports"], args.original, tree):
        source_id = tree["src/" + relative(name, ".lean").as_posix()]
        inventory[name] = [source_id, digest((args.library / relative(name, ".olean")).read_bytes())]
    signature = digest((json.dumps(inventory, sort_keys=True, indent=2) + "\n").encode())
    if signature != src_closure["source_blob_and_object_inventory_sha256"]:
        raise RuntimeError("Imported project object inventory differs.")
    if args.representatives:
        roots = ["Formalism.SharpRestriction.GlobalSchurBounds.MainIn",
                 "Development.AutomorphicArithmetic.MeanSquareBounds.TwistPrim",
                 "Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts"]
        module = "ClassRepresentatives"
        axioms = ["three_representatives"]
    else:
        roots = ["Formalism.SharpRestriction.GlobalSchurBounds.MainIn",
                 "Development.AutomorphicArithmetic.MeanSquareBounds.PsiThin"]
        module = "BoxedClassPsi"
        axioms = ["noExc_of_goodFor", "noExc_of_boxes", "family_psi_estimate", "conductor_envelope",
                  "envelope_tends_to_zero"]
    graph = closure(roots, args.original, tree)
    if not set(graph) <= inventory.keys():
        raise RuntimeError("Missing authenticated original dependency.")
    source = Path(__file__).with_name(module + ".lean").read_bytes()
    with TemporaryDirectory() as tmp:
        work = Path(tmp)
        def run(command):
            proc = subprocess.run(command, cwd=work, env=env, capture_output=True, text=True)
            out = (proc.stdout + proc.stderr).strip()
            if proc.returncode or "declaration uses 'sorry'" in out:
                raise RuntimeError(out)
            return out
        env["LEAN_PATH"] = os.pathsep.join([str(work), str(args.library), env["LEAN_PATH"]])
        (work / (module + ".lean")).write_bytes(source)
        log = run([args.toolchain / "bin/lean", *FLAGS, "--root=.", "-o", module + ".olean", module + ".lean"])
        lines = re.sub(r"\n[ \t]+", " ", log).splitlines()
        expected = {f"'Uriel.ServedPrime.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                    for name in axioms}
        if len(lines) != len(axioms) or set(lines) != expected:
            raise RuntimeError(log)
        checked = {}
        for name in roots + [module]:
            kernel_log = run([args.toolchain / "bin/leanchecker", "-v", name])
            if kernel_log != "replaying " + name:
                raise RuntimeError(kernel_log)
            checked[name] = kernel_log
        print(json.dumps({"pin": PIN, "toolchain": version, "flags": FLAGS, "original_inventory": signature,
                          "original_inventory_modules": len(inventory),
                          "original_direct_import_closure": len(graph), "original_direct_imports": roots,
                          "module": module, "supplement_sha256": digest(source),
                          "supplement_olean_sha256": digest((work / (module + ".olean")).read_bytes()),
                          "axioms": lines, "kernel_replays": checked}, indent=2))


if __name__ == "__main__":
    main()
