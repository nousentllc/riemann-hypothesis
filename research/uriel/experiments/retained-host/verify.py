"""Authenticate the pinned source and replay the retained-host experiments in a fresh library."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from graphlib import TopologicalSorter
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from strengthen import generate

HERE = Path(__file__).resolve().parent
JOINT = HERE.parent / "joint-witness"
sys.path.insert(0, str(JOINT))
from build_original import FLAGS, PIN, ROOT, closure, environment, pinned_source, pinned_tree, relative

PARENT = "e674cb750ef96b2f5e7cd46586ea4edb9998715a"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
PACKAGES = {"Mathlib", "Lean", "Init", "Std"}
AXIOMS = re.compile(r"'([^'\n]+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
REQUIRED = {"Construction", "StrongWindow", "HostHandoff", "StrongSupply", "Audit", "ShareControl", "ShareMargin"}


def digest(data):
    return sha256(data).hexdigest()


def canonical(obj):
    return (json.dumps(obj, allow_nan=False, indent=2, sort_keys=True) + "\n").encode()


def parent_bytes(path):
    return subprocess.check_output(["git", "-C", ROOT, "show", f"{PARENT}:{path.relative_to(ROOT).as_posix()}"])


def imports(data):
    result = set()
    for line in re.findall(r"(?m)^(?:public )?import[ \t]+([^\n]+)", data.decode()):
        for module in line.partition("--")[0].split():
            if not re.fullmatch(r"\w+(?:\.\w+)*", module):
                raise ValueError("Unsupported import syntax " + line)
            if module.split(".")[0] not in PACKAGES:
                result.add(module)
    return sorted(result)


def invoke(command, src, env):
    call = subprocess.run(command, cwd=src, env=env, capture_output=True, text=True)
    log = (call.stdout + call.stderr).strip()
    if call.returncode or "declaration uses 'sorry'" in log or "sorryAx" in log:
        raise RuntimeError(f"{command[-1]}\n{log}")
    return log


def schedule(graph, workers, action):
    order = TopologicalSorter(graph)
    order.prepare()
    running = {}
    with ThreadPoolExecutor(max_workers=workers) as pool:
        while order.is_active():
            for module in sorted(order.get_ready()):
                running[pool.submit(action, module)] = module
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for task in done:
                task.result()
                order.done(running.pop(task))


def run(args):
    if args.work.exists() and any(args.work.iterdir()):
        raise ValueError("Use an empty work directory for a fresh isolated library")
    args.work.mkdir(parents=True, exist_ok=True)
    src, lib = args.work / "src", args.work / "lib"
    src.mkdir()
    lib.mkdir()
    tc = args.toolchain
    env, version = environment(tc, args.mathlib)
    env["LEAN_PATH"] = str(lib) + os.pathsep + env["LEAN_PATH"]
    tree = pinned_tree()
    records, known = {}, {}
    manifests = {}
    for record_name in ("original_build", "bridge_build", "join_checks"):
        data = parent_bytes(JOINT / "results" / (record_name + ".json"))
        manifests[record_name] = digest(data)
        record = json.loads(data)
        if record["pin"] != PIN or record["toolchain"]["lean"] != version["lean"] or record["toolchain"]["packages"] != version["packages"]:
            raise ValueError("Pinned source, compiler, or package revision mismatch in " + record_name)
        records[record_name] = record
        # Cross-platform replays can compile all original sources. Object reuse is platform-specific.
        if record_name != "join_checks" and record["toolchain"] == version:
            for name, row in record["modules"].items():
                if name in known and known[name] != row:
                    raise ValueError("Conflicting prior records for " + name)
                known[name] = row

    generated = generate(args.source, tree)
    local = {path.stem: path.read_bytes() for path in sorted(HERE.glob("*.lean"))}
    if local.keys() & generated.keys():
        raise ValueError("A generated module shadows a local experiment file")
    kinds = {k: "experiment" for k in local} | {k: "generated" for k in generated}
    local.update(generated)
    if REQUIRED - local.keys():
        raise ValueError("Missing experiment modules: " + str(sorted(REQUIRED - local.keys())))
    prior = records["join_checks"]["local"]
    dependencies = [dep for data in local.values() for dep in imports(data)]
    while dependencies:
        name = dependencies.pop()
        if name in local or name not in prior:
            continue
        data = parent_bytes(JOINT / (name + ".lean"))
        if digest(data) != prior[name]["source_sha256"]:
            raise ValueError("Prior local source hash mismatch " + name)
        local[name] = data
        kinds[name] = "parent"
        dependencies.extend(imports(data))
    local_deps = {name: imports(data) for name, data in local.items()}
    targets = sorted({dep for deps in local_deps.values() for dep in deps if dep not in local})
    graph = closure(targets, args.source, tree, src)
    for name, data in local.items():
        path = src / relative(name, ".lean")
        if path.exists():
            raise ValueError("Local module shadows a pinned original: " + name)
        path.write_bytes(data)

    def compile_one(name):
        rel = relative(name, ".lean")
        obj = lib / relative(name, ".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        log = invoke([tc / "bin/lean", *FLAGS, "--root=.", "-o", obj, rel], src, env)
        return digest(obj.read_bytes()), log

    original_objects = {}
    rebuilt = {}
    for name in sorted(graph):
        row = known.get(name)
        if row is None:
            continue
        if row["source_blob"] != tree["src/" + relative(name, ".lean").as_posix()]:
            raise ValueError("Original source identity mismatches prior build for " + name)
        for cache in args.cache_lib:
            path = cache / relative(name, ".olean")
            if not path.is_file():
                continue
            data = path.read_bytes()
            if digest(data) != row["olean_sha256"]:
                raise ValueError("Cached object digest mismatch for " + name)
            destination = lib / relative(name, ".olean")
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(data)
            original_objects[name] = row["olean_sha256"]
            break
    missing = {name: [dep for dep in deps if dep not in original_objects]
               for name, deps in graph.items() if name not in original_objects}
    print(f"Original closure {len(graph)}; authenticated objects reused {len(original_objects)}; rebuilding {len(missing)}.", flush=True)

    def build_original(name):
        obj_hash, _ = compile_one(name)
        original_objects[name] = obj_hash
        rebuilt[name] = obj_hash

    schedule(missing, args.workers, build_original)
    inventory = {n: [tree["src/" + relative(n, ".lean").as_posix()], original_objects[n]] for n in graph}
    report = {"pin": PIN, "parent": PARENT, "toolchain": version, "flags": FLAGS, "prior_manifest_sha256": manifests,
              "source_closure": {"original_modules": len(graph), "direct_original_imports": targets,
                                 "source_blob_and_object_inventory_sha256": digest(canonical(inventory)),
                                 "original_objects_reused": len(graph)-len(missing), "original_objects_rebuilt": rebuilt},
              "local": {}, "audit_edges": [], "finite": {}}

    def build_local(name):
        obj_hash, log = compile_one(name)
        replay = invoke([tc / "bin/leanchecker", "-v", name], src, env)
        if replay != "replaying " + name:
            raise ValueError("Unexpected replay transcript for " + name)
        axioms = {n: sorted(x.strip() for x in deps.split(",") if x.strip()) for n, deps in AXIOMS.findall(log)}
        requests = re.findall(rb"(?m)^#print axioms\s+(\S+)", local[name])
        if len(axioms) != len(requests):
            raise ValueError("Unexpected printed axioms in " + name + "\n" + log)
        row = {"kind": kinds[name], "source_sha256": digest(local[name]), "olean_sha256": obj_hash,
               "direct_imports": local_deps[name], "replay": replay, "printed_axioms": axioms}
        if name == "Audit":
            edges = [json.loads(line.removeprefix("RETAINED_EDGE ")) for line in log.splitlines()
                     if line.startswith("RETAINED_EDGE ")]
            if len(edges) < 15 or len({canonical(edge) for edge in edges}) != len(edges):
                raise ValueError("Expected at least 15 distinct authenticated audit rows")
            if any(set(edge["axioms"])-STANDARD for edge in edges):
                raise ValueError("Unexpected axiom in source edge inventory")
            report["audit_edges"] = edges
        report["local"][name] = row
        print("Replayed " + name, flush=True)

    local_graph = {n: [d for d in deps if d in local] for n, deps in local_deps.items()}
    schedule(local_graph, args.workers, build_local)
    # Inspect actual environment constants. Pretty-printed axiom names may be shortened by open namespaces.
    header = "".join("import " + module + "\n" for module in sorted(local))
    names = "[" + ", ".join(json.dumps(n) for n in sorted(local)) + "]"
    body = r"""
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let wanted : List String := MODULES
  let env ← getEnv
  let selected := env.header.moduleNames.map (fun n => wanted.contains n.toString)
  let rows := env.constants.map₁.fold (init := #[]) fun rows n info => Id.run do
    let some idx := env.getModuleIdxFor? n | return rows
    unless selected[idx]! do return rows
    match info with
    | .thmInfo _ | .axiomInfo _ => return rows.push (env.header.moduleNames[idx]!, n)
    | _ => return rows
  for (mod, n) in rows do
    let ax := ((← collectAxioms n).map Name.toString).qsort (· < ·)
    IO.println ("AXIOM_ROW " ++ (Json.mkObj [("module", toJson mod.toString),
      ("declaration", toJson n.toString), ("axioms", toJson ax)]).compress)
"""
    auditor = src / "RetainedAxiomInventory.lean"
    auditor.write_text(header + body.replace("MODULES", names))
    inventory_log = invoke([tc / "bin/lean", *FLAGS, "--root=.", auditor.name], src, env)
    inventory_rows = [json.loads(line.removeprefix("AXIOM_ROW ")) for line in inventory_log.splitlines()
                      if line.startswith("AXIOM_ROW ")]
    if not inventory_rows or any(set(row["axioms"]) - STANDARD for row in inventory_rows):
        raise ValueError("Unexpected or absent axiom inventory")
    for name, metadata in report["local"].items():
        table = {row["declaration"]: row["axioms"] for row in inventory_rows if row["module"] == name}
        if metadata["printed_axioms"] and not table:
            raise ValueError("Empty theorem inventory for " + name)
        del metadata["printed_axioms"]
        metadata["theorem_axioms"] = table
    report["axiom_auditor_sha256"] = digest(auditor.read_bytes())
    actual = subprocess.check_output([sys.executable, "-B", str(HERE / "share_counts.py")])
    expected = (HERE / "share_counts.json").read_bytes()
    if expected != actual:
        raise ValueError("Exact-rational enumeration differs from the published results")
    report["finite"] = {"enumeration_source_sha256": digest((HERE/"share_counts.py").read_bytes()),
                        "result_sha256": digest(actual), "byte_match": True}
    report["scope"] = "leanchecker replay of recorded local, generated and parent modules against the authenticated targeted project closure and pinned package environment"
    args.out.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.out.with_suffix(".json.tmp")
    temporary.write_bytes(canonical(report))
    temporary.replace(args.out)
    print(f"Verified {len(local)} Lean modules and {len(report['audit_edges'])} proof edges.", flush=True)


def main():
    arg = argparse.ArgumentParser(description=__doc__)
    for name in ("source", "toolchain", "mathlib", "work"):
        arg.add_argument("--" + name, type=lambda s: Path(s).resolve(), required=True)
    arg.add_argument("--cache-lib", type=lambda s: Path(s).resolve(), action="append", default=[])
    arg.add_argument("--workers", type=int, default=3)
    arg.add_argument("--out", type=Path, default=HERE / "results" / "verification.json")
    args = arg.parse_args()
    if args.workers < 1:
        arg.error("--workers must be positive")
    run(args)


if __name__ == "__main__":
    main()
