"""Replay the weighted-orbit supplement against the retained-host experiment."""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory


def checksum(data):
    return sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("checkout", "original", "toolchain", "mathlib", "library"):
        parser.add_argument("--" + key, required=True, type=lambda p: Path(p).resolve())
    parser.add_argument("--manifest", type=Path,
                        help="Use the verification record of your own public experiment replay.")
    args = parser.parse_args()
    xp = args.checkout / "research/uriel/experiments"
    sys.path.insert(0, str(xp / "joint-witness"))
    from build_original import FLAGS, PIN, closure, environment, pinned_tree, relative

    manifest = args.manifest or xp / "retained-host/results/verification.json"
    record = json.loads(manifest.read_bytes())
    env, version = environment(args.toolchain, args.mathlib)
    if (record["pin"], record["flags"], record["toolchain"]) != (PIN, FLAGS, version):
        raise ValueError("Use the matching toolchain and public replay manifest.")
    tree = pinned_tree()
    roots = record["source_closure"]["direct_original_imports"]
    graph = closure(roots, args.original, tree)
    inventory = {}
    for name in graph:
        obj = args.library / relative(name, ".olean")
        blob = tree["src/" + relative(name, ".lean").as_posix()]
        inventory[name] = [blob, checksum(obj.read_bytes())]
    data = (json.dumps(inventory, allow_nan=False, indent=2, sort_keys=True) + "\n").encode()
    if checksum(data) != record["source_closure"]["source_blob_and_object_inventory_sha256"]:
        raise ValueError("The original module inventory differs from the public replay.")
    direct = ["Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound"]
    actual_imports = closure(direct, args.original, tree)
    if not actual_imports.keys() <= inventory.keys():
        raise ValueError("This supplement needs modules outside the authenticated inventory.")
    lean_source = Path(__file__).with_name("OrbitBudget.lean").read_bytes()
    digest = checksum(lean_source)
    if digest != "671cac77a830289b1c41104e653779f42db1335a75094e87ddfb55ce6c8ee74a":
        raise ValueError("Supplement source differs from the reported replay.")
    with TemporaryDirectory() as tmp:
        work = Path(tmp)
        (work / "OrbitBudget.lean").write_bytes(lean_source)
        env["LEAN_PATH"] = os.pathsep.join((str(work), str(args.library), env["LEAN_PATH"]))
        compiler = args.toolchain / "bin/lean"
        checker = args.toolchain / "bin/leanchecker"
        compile_args = [compiler, *FLAGS, "--root=.", "-o", "OrbitBudget.olean", "OrbitBudget.lean"]
        commands = [compile_args, [checker, "-v", "OrbitBudget"]]
        logs = [subprocess.check_output(cmd, cwd=work, env=env, text=True, stderr=subprocess.STDOUT).strip()
                for cmd in commands]
        expected = {f"'OrbitAudit.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                    for name in ("every_arrangement_good", "one_tile_iff", "good_one_tile_iff", "width_two_marked_iff", "tiles_iff_exists",
                                 "eligible_update", "badPoints_by_representative", "mass_zero_iff",
                                 "badOK_singleton_iff", "badOK_zero_iff")}
        if set(logs[0].splitlines()) != expected or logs[1] != "replaying OrbitBudget":
            raise ValueError("Unexpected elaboration or kernel output:\n" + "\n".join(logs))
        print(json.dumps({"source_sha256": digest, "public_pin": PIN,
                          "public_objects_authenticated": len(inventory),
                          "supplement_original_import_closure": len(actual_imports),
                          "toolchain": version["lean"], "output": logs}, indent=2))


if __name__ == "__main__":
    main()
