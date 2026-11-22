"""Rebuild or authenticate the original dependencies, compile the experiment and replay its declarations."""
import argparse
from graphlib import TopologicalSorter
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
JOINT = HERE.parent / "joint-witness"
sys.path.insert(0, str(JOINT))
from build_original import FLAGS, PIN, closure, dump, environment, pinned_tree, relative

ORIGINAL = [
    "Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Exc",
    "Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply",
]


def check(args):
    work, tc = args.work.resolve(), args.toolchain.resolve()
    if work.exists() and any(work.iterdir()):
        raise ValueError("Use a new or empty work directory")
    src, lib = work / "src", work / "lib"
    src.mkdir(parents=True, exist_ok=True)
    lib.mkdir(exist_ok=True)
    tree = pinned_tree()
    graph = closure(ORIGINAL, args.source.resolve(), tree, src)
    env, version = environment(tc, args.mathlib.resolve())
    env["LEAN_PATH"] = str(lib) + os.pathsep + env["LEAN_PATH"]
    manifest = {}
    if args.cache:
        for filename in ("original_build.json", "bridge_build.json"):
            prior = json.loads((JOINT / "results" / filename).read_text())
            if prior["pin"] != PIN or prior["toolchain"] != version:
                raise ValueError("Prior toolchain or source differs")
            manifest.update(prior["modules"])
    result = {"pin": PIN, "toolchain": version, "flags": FLAGS, "modules": {}, "replays": {}}

    def run(command, *, control=False):
        p = subprocess.run(command, cwd=src, env=env, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if control:
            if p.returncode == 0 or "type mismatch" not in p.stdout.lower():
                raise RuntimeError(p.stdout)
        elif p.returncode or "sorryAx" in p.stdout or "declaration uses 'sorry'" in p.stdout:
            raise RuntimeError(p.stdout)
        return p.stdout.strip()

    for mod in TopologicalSorter(graph).static_order():
        dest = lib / relative(mod, ".olean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        source_id = tree["src/" + relative(mod, ".lean").as_posix()]
        if mod in manifest:
            record = manifest[mod]
            origin = args.cache.resolve() / relative(mod, ".olean")
            if record["source_blob"] != source_id or sha256(origin.read_bytes()).hexdigest() != record["olean_sha256"]:
                raise ValueError("Source or compiled hash differs for " + mod)
            shutil.copyfile(origin, dest)
            mode = "authenticated cache"
        else:
            run([tc/"bin/lean", *FLAGS, "--root=.", "-o", dest, relative(mod, ".lean")])
            mode = "freshly compiled"
        result["modules"][mod] = {"source_blob": source_id, "olean_sha256": sha256(dest.read_bytes()).hexdigest(),
                                  "mode": mode}
    new = "SlotThree"
    local_source = HERE / (new + ".lean")
    local_bytes = local_source.read_bytes()
    (src / local_source.name).write_bytes(local_bytes)
    obj = lib/(new+".olean")
    log = run([tc/"bin/lean", *FLAGS, "--root=.", "-o", obj, local_source.name])
    declarations = re.findall(r"(?m)^#print axioms (SlotThree\.\w+)$", local_bytes.decode())
    for decl in declarations:
        m = re.search(r"'" + re.escape(decl) + r"' depends on axioms: \[([^\]]*)\]", log)
        if not m or (set(m.group(1).split(", ")) - {"propext", "Classical.choice", "Quot.sound"}):
            raise ValueError(f"Unexpected axiom inventory at {decl}: {log}")
    result["local"] = {"module": new, "source_sha256": sha256(local_bytes).hexdigest(),
                       "olean_sha256": sha256(obj.read_bytes()).hexdigest(), "compiler_output": log}
    for name in [*ORIGINAL, new]:
        output = run([tc/"bin/leanchecker", "-v", name])
        if output != "replaying " + name:
            raise ValueError(output)
        result["replays"][name] = output
    control = """import SlotThree
open UpperTheory.V.Win
example {L : Type} [Field L] {R c : ℕ}
    (h : ∃ E : Finset ℕ, FirstBound 3 R c L 64 E) :
    ∃ E : Finset ℕ, 1 ∈ E ∧ FirstBound 3 R c L 64 E := h
"""
    (src/"Control.lean").write_text(control)
    result["rejected_direct_positive_membership"] = run([tc/"bin/lean", *FLAGS, "Control.lean"], control=True)
    dump(args.out, result)
    print(f"Verified {len(graph)} original source modules, {len(declarations)} local axiom inventories, "
          f"{len(result['replays'])} kernel replays and the rejected substitution.")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for label in ("toolchain", "source", "mathlib", "work", "out"):
        ap.add_argument("--"+label, type=Path, required=True)
    ap.add_argument("--cache", type=Path, help="Single assembled lib directory from the previous bridge run")
    check(ap.parse_args())


if __name__ == "__main__":
    main()
