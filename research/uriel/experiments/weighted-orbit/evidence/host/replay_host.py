"""Authenticate the pinned source and compiled inputs, then replay the concrete host module."""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("checkout", "original", "toolchain", "mathlib", "library"):
        parser.add_argument("--" + name, required=True, type=lambda p: Path(p).resolve())
    parser.add_argument("--manifest", type=Path, help="Verification record from a fresh replay on your platform.")
    args = parser.parse_args()
    experiments = args.checkout / "research/uriel/experiments"
    sys.path.insert(0, str(experiments / "joint-witness"))
    from build_original import FLAGS, PIN, closure, environment, pinned_tree, relative

    manifest = args.manifest or experiments / "retained-host/results/verification.json"
    record = json.loads(manifest.read_bytes())
    env, version = environment(args.toolchain, args.mathlib)
    if (record["pin"], record["flags"], record["toolchain"]) != (PIN, FLAGS, version):
        raise ValueError("The local tools differ from the pinned public record.")
    tree = pinned_tree()
    public = record["source_closure"]
    graph = closure(public["direct_original_imports"], args.original, tree)
    inventory = {}
    for name in graph:
        obj = args.library / relative(name, ".olean")
        source_blob = tree["src/" + relative(name, ".lean").as_posix()]
        inventory[name] = [source_blob, sha256(obj.read_bytes()).hexdigest()]
    serialized = (json.dumps(inventory, indent=2, sort_keys=True) + "\n").encode()
    inventory_digest = sha256(serialized).hexdigest()
    if inventory_digest != public["source_blob_and_object_inventory_sha256"]:
        raise ValueError("The source and object inventory differs from the public replay.")
    source = Path(__file__).with_name("ConcreteOrbitHost.lean")
    content = source.read_bytes()
    imports = [line.split()[1] for line in content.decode().splitlines() if line.startswith("import ")]
    for module in imports:
        if not module.startswith("Mathlib.") and module not in inventory:
            raise ValueError(f"Original import outside the authenticated source closure: {module}.")
    with TemporaryDirectory() as tmp:
        work = Path(tmp)
        (work / source.name).write_bytes(content)
        env["LEAN_PATH"] = os.pathsep.join((str(work), str(args.library), env["LEAN_PATH"]))
        name = source.stem
        commands = [[args.toolchain / "bin/lean", *FLAGS, "--root=.", "-o", name+".olean", source.name],
                    [args.toolchain / "bin/leanchecker", "-v", name]]
        logs = [subprocess.check_output(cmd, env=env, cwd=work, text=True,
                                        stderr=subprocess.STDOUT).strip() for cmd in commands]
        expected = {f"'Uriel.OrbitHost.host{e}_exists' depends on axioms: [propext, Classical.choice, Quot.sound]"
                    for e in (13, 15, 17, 64)}
        expected.add("'Uriel.OrbitHost.chosen_step_eq_artin' depends on axioms: [propext, Classical.choice, Quot.sound]")
        if set(logs[0].splitlines()) != expected or logs[1] != "replaying " + name:
            raise ValueError("Unexpected compiler or kernel receipt:\n" + "\n".join(logs))
        print(json.dumps({"pin": PIN, "toolchain": version["lean"], "module": name,
                          "source_sha256": sha256(content).hexdigest(),
                          "imported_original_modules_authenticated": len(inventory),
                          "public_source_object_inventory_sha256": inventory_digest,
                          "direct_imports": imports, "kernel_receipts": logs}, indent=2))


if __name__ == "__main__":
    main()
