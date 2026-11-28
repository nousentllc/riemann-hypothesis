"""Build, kernel-replay and audit the class-number and witness experiments."""
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
import tomllib

HERE = Path(__file__).resolve().parent
SLOT = HERE.parent / "slot-three"
sys.path.insert(0, str(HERE.parent / "joint-witness"))
from build_original import FLAGS, PIN, ROOT, closure, environment, pinned_source, pinned_tree, relative
from check_excerpt import verify as check_excerpt

PARENT = "4b1c9fbbfb9bc50a3f791c2c1f3d7f2adb336c87"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
PACKAGES = {"Init", "Lean", "Mathlib", "Std"}
FINAL_RESULTS = {"SlotThree.Complete." + name for name in (
    "ascend", "regular_layer", "towerClass", "standard_layers", "opposite_at_64", "all_labels_are_admissible",
    "same_lift_unconditional", "fixed_class_divisibility", "coinvariant_norm_injective", "fixed_class_count",
    "norm_on_coinvariants_bijective", "layer_invariant_zero", "partB_named_center",
)}
REQUIRED_BY_MODULE = {"TowerResult": FINAL_RESULTS, "SharedLift": {"SlotThree.Complete.shared_lift_all_labels"}}


def digest(data):
    return sha256(data).hexdigest()


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(".tmp")
    temp.write_text(json.dumps(value, indent=2, sort_keys=True, allow_nan=False) + "\n")
    temp.replace(path)


def git(*args):
    return subprocess.check_output(["git", "-C", ROOT, *args])


def module_imports(data):
    imports = []
    for line in re.findall(r"(?m)^(?:public )?import[ \t]+([^\n]+)", data.decode()):
        for name in line.split("--")[0].split():
            if not re.fullmatch(r"\w+(?:\.\w+)*", name):
                raise ValueError("Unsupported import expression " + line)
            if name.split(".")[0] not in PACKAGES:
                imports.append(name)
    return imports


def invoke(args, src, env, *, reject=False):
    call = subprocess.run(args, cwd=src, env=env, text=True, capture_output=True)
    log = (call.stdout + call.stderr).strip()
    if reject:
        if call.returncode == 0 or "type mismatch" not in log.lower():
            raise ValueError("Expected a type mismatch\n" + log)
    elif call.returncode or "declaration uses 'sorry'" in log or "sorryAx" in log:
        raise ValueError("Failed Lean check\n" + log)
    return log


def install(src, dest, checksum):
    if digest(src.read_bytes()) != checksum:
        raise ValueError("Prior object digest mismatch for " + str(src))
    if dest.exists():
        if digest(dest.read_bytes()) != checksum:
            raise ValueError("Unexpected object already in scratch library " + str(dest))
        return
    dest.parent.mkdir(parents=True, exist_ok=True)
    try:
        os.link(src, dest)
    except OSError:
        shutil.copyfile(src, dest)


def prepare(args):
    args.work.mkdir(parents=True, exist_ok=True)
    stamp = args.work / "ascent-build-v1"
    if not stamp.exists():
        if any(args.work.iterdir()):
            raise ValueError("Use a fresh work directory or an existing work directory from this driver")
        stamp.write_text(PIN + "\n")
    if stamp.read_text().strip() != PIN:
        raise ValueError("Mismatched scratch directory")
    src, lib = args.work / "src", args.work / "lib"
    src.mkdir(exist_ok=True)
    lib.mkdir(exist_ok=True)
    env, version = environment(args.toolchain, args.mathlib)
    env["LEAN_PATH"] = str(lib) + os.pathsep + env["LEAN_PATH"]
    manifests = {}
    for key, path in (("tower", args.tower_manifest), ("slot", args.slot_manifest)):
        record = json.loads(path.read_bytes())
        if record["pin"] != PIN or record["toolchain"] != version or record["flags"] != FLAGS:
            raise ValueError("Incompatible source, toolchain or flags in " + str(path))
        manifests[key] = record
    tree = pinned_tree()
    local = {p.stem:p.read_bytes() for p in sorted(HERE.glob("*.lean"))}
    shadowed = set(local) & (manifests["slot"]["modules"].keys() | PACKAGES)
    if shadowed:
        raise ValueError("A new module would shadow an imported module: " + repr(shadowed))
    parents, slot_data, original_targets, local_graph = set(), {}, set(), {}
    targets = set(args.targets or local)
    if targets - local.keys():
        raise ValueError("Unknown requested modules " + repr(targets - local.keys()))
    if not args.targets and REQUIRED_BY_MODULE.keys() - targets:
        raise ValueError("A required result module is missing")
    pending = list(targets)
    while pending:
        name = pending.pop()
        if name in local_graph or name in parents:
            continue
        if name in local:
            inputs = module_imports(local[name])
            local_graph[name] = [dep for dep in inputs if dep in local]
        elif name in manifests["slot"]["modules"]:
            parents.add(name)
            path = (SLOT / (name + ".lean")).relative_to(ROOT).as_posix()
            data = git("show", PARENT + ":" + path)
            slot_data[name] = data
            inputs = module_imports(data)
        else:
            original_targets.add(name)
            continue
        pending.extend(inputs)
    graph = closure(original_targets, args.source, tree)
    config = tomllib.loads(git("show", PIN + ":lakefile.toml").decode())
    section = next(s for s in config["lean_lib"] if s["name"] == "GroundTheoryFields")
    field_flags = {g.removesuffix("+"): "-DsynthInstance.maxHeartbeats="+
                   str(section["leanOptions"]["synthInstance"]["maxHeartbeats"]) for g in section["globs"]}
    orig_hash = sha256()
    missing = {}
    cached = manifests["tower"]["modules"]
    for name in sorted(graph):
        path = relative(name, ".lean")
        if name not in cached:
            missing[name] = [dep for dep in graph[name] if dep not in cached]
            continue
        row = cached[name]
        blob = tree["src/" + path.as_posix()]
        if row["source_blob"] != blob:
            raise ValueError("Mismatched source record for " + name)
        if any(name.startswith(prefix) for prefix in field_flags):
            if manifests["tower"]["additional_flags_by_prefix"] != field_flags:
                raise ValueError("Mismatched per-library compiler settings")
        obj = relative(name, ".olean")
        install(args.tower / "lib" / obj, lib / obj, row["olean_sha256"])
        orig_hash.update((name + " " + blob + " " + row["olean_sha256"] + "\n").encode())
    parent_rows = {}
    for name in sorted(parents):
        row = manifests["slot"]["modules"][name]
        if row["source_sha256"] != digest(slot_data[name]):
            raise ValueError("Unexpected earlier experiment source " + name)
        install(args.slot / "lib" / (name+".olean"), lib / (name+".olean"), row["olean_sha256"])
        parent_rows[name] = {"source_sha256":row["source_sha256"], "olean_sha256":row["olean_sha256"]}
    seed = dict(pin=PIN, parent=PARENT, flags=FLAGS, toolchain=version, field_flags=field_flags,
        tower_manifest_sha256=digest(args.tower_manifest.read_bytes()), slot_manifest_sha256=digest(args.slot_manifest.read_bytes()),
        original_closure=len(graph), original_reused=len(graph)-len(missing), original_reused_digest=orig_hash.hexdigest(),
        parent_modules=parent_rows, excerpt=check_excerpt(args.source))
    return src, lib, env, local, local_graph, missing, tree, seed


def read_printed_axioms(source, log):
    count = len(re.findall(r"(?m)^#print\s+axioms\s+", source.decode()))
    records = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    if len(records) != count:
        raise ValueError("Incomplete #print axioms transcript\n" + log[:3000])
    for name, axioms in records:
        if {a.strip() for a in axioms.split(",") if a.strip()} - STANDARD:
            raise ValueError("Unexpected axiom for " + name)
    return sorted(name for name, _ in records)


def audit_modules(names, args, src, env):
    lines = ["import "+name for name in names] + ["import Lean.Util.CollectAxioms"]
    lines += ["open Lean Elab Command", "run_cmd do", "  let env ← getEnv",
              "  for mod in "+json.dumps(names)+" do",
              '    let some idx := env.getModuleIdx? mod.toName | throwError "Missing {mod}"',
              "    for c in env.header.moduleData[idx.toNat]!.constants do",
              "      if c.isTheorem || c.isAxiom then",
              "        let xs := (← collectAxioms c.name).map Name.toString",
              '        let row := Json.mkObj [("module", toJson mod), ("name", toJson c.name.toString), ("axioms", toJson xs)]',
              '        IO.println ("ASCENT_AXIOMS " ++ row.compress)']
    (src/"AscentAuditRun.lean").write_text("\n".join(lines)+"\n")
    output = invoke([args.toolchain/"bin/lean", *FLAGS, "AscentAuditRun.lean"], src, env)
    inventory = {m:[] for m in names}
    for line in output.splitlines():
        if line.startswith("ASCENT_AXIOMS "):
            data = json.loads(line.removeprefix("ASCENT_AXIOMS "))
            if set(data["axioms"]) - STANDARD:
                raise ValueError("Nonstandard axiom in " + data["name"])
            inventory[data["module"]].append((data["name"],sorted(data["axioms"])))
    for mod, required in REQUIRED_BY_MODULE.items():
        if mod not in names:
            continue
        missing = required - {name for name, _ in inventory[mod]}
        if missing:
            raise ValueError("Final theorem missing from the kernel environment: " + repr(sorted(missing)))
    return {mod:{"declarations": len(rows), "axiom_set":sorted({ax for _, xs in rows for ax in xs}),
                 "inventory_sha256":digest(json.dumps(sorted(rows),separators=(",",":")).encode())}
            for mod, rows in inventory.items()}


def controls(args, src, env, names):
    tests = {}
    if "UpstairsExtension" in names:
        tests["change_base_of_unramifiedness"] = (
            "import UpstairsExtension\nopen GroundTheory.Global Ascent.Upstairs\n"
            "example (E : Type) [Field E] [NumberField E] : IsUnramifiedEverywhere BASE (Elementary E (AlgebraicClosure E)) :=\n"
            "  elementary_unramified E (AlgebraicClosure E)\n", "BASE", "E", "ℚ")
    if "WitnessRecord" in names:
        tests["anonymous_set_membership"] = (
            "import WitnessRecord\nopen UpperTheory.V.Win\n"
            "example (S : Finset ℕ) (h : FirstBound 3 1 1 SlotThree.L 64 S) : TARGET := h\n",
            "TARGET", "FirstBound 3 1 1 SlotThree.L 64 S", "1 ∈ S")
    if "TowerResult" in names:
        tests["all_layer_premise"] = (
            "import TowerResult\nexample : SlotThree.TowerClassHyp := PROOF\n",
            "PROOF", "SlotThree.Complete.towerClass", "SlotThree.BaseField.three_not_dvd_class_card")
    records = {}
    for name, (body, token, good, bad) in tests.items():
        f = src/"AscentControlRun.lean"
        cmd = [args.toolchain/"bin/lean",*FLAGS,f.name]
        f.write_text(body.replace(token,good))
        invoke(cmd,src,env)
        f.write_text(body.replace(token,bad))
        log = invoke(cmd,src,env,reject=True)
        records[name] = {"accepted_type":good, "rejected_type":bad, "rejection":log}
    return records


def run(args):
    src, lib, env, local, local_graph, missing, tree, seed = prepare(args)
    checkpoint = args.work/"compiled.json"
    previous = json.loads(checkpoint.read_bytes()) if checkpoint.is_file() else {}
    done = {}
    sig = digest(json.dumps({k:seed[k] for k in ("toolchain","flags","field_flags","original_reused_digest","parent_modules")},
                            sort_keys=True).encode())
    def compile_module(name, data, inputs, flags, is_local):
        path, obj_path = relative(name,".lean"), relative(name,".olean")
        source, obj = src/path, lib/obj_path
        source.parent.mkdir(parents=True,exist_ok=True)
        obj.parent.mkdir(parents=True,exist_ok=True)
        row = {"source_sha256":digest(data), "inputs":{dep:done[dep]["olean_sha256"] for dep in sorted(inputs)},
               "build_context":sig}
        prior = previous.get(name,{})
        if (all(prior.get(k)==v for k,v in row.items()) and obj.exists() and
                prior.get("olean_sha256")==digest(obj.read_bytes()) and prior.get("replay")=="replaying "+name):
            done[name]=prior
            print("verified checkpoint",name,flush=True)
            return
        source.write_bytes(data)
        temp = obj.parent/(obj.stem+".new.olean")
        log = invoke([args.toolchain/"bin/lean",*FLAGS,*flags,"--root=.","-o",temp,path],src,env)
        temp.replace(obj)
        replay = invoke([args.toolchain/"bin/leanchecker","-v",name],src,env)
        if replay!="replaying "+name:
            raise ValueError("Incomplete replay "+name)
        row.update(olean_sha256=digest(obj.read_bytes()), replay=replay)
        if is_local:
            row["printed_axioms"]=read_printed_axioms(data,log)
        else:
            row["source_blob"]=tree["src/"+path.as_posix()]
        done[name]=row
        previous[name]=row
        save(checkpoint,previous)
        print(replay,flush=True)
    print("Original closure",seed["original_closure"],"new original modules",len(missing),flush=True)
    for name in TopologicalSorter(missing).static_order():
        path=relative(name,".lean")
        extra_flags=[flag for pref,flag in seed["field_flags"].items() if name.startswith(pref)]
        compile_module(name,pinned_source(Path("src")/path,args.source,tree),missing[name],extra_flags,False)
    for name in TopologicalSorter(local_graph).static_order():
        inputs=local_graph[name]+[dep for dep in module_imports(local[name]) if dep in missing]
        compile_module(name,local[name],inputs,[],True)
    names=sorted(local_graph)
    inventory=audit_modules(names,args,src,env)
    if any(inventory[m]["declarations"] == 0 for m in names):
        raise ValueError("Empty axiom inventory")
    if not args.targets and set(local) != {p.stem for p in HERE.glob("*.lean")}:
        raise ValueError("Module set changed during the run")
    for name in names:
        if (HERE/(name+".lean")).read_bytes()!=local[name]:
            raise ValueError("Source changed during the run: "+name)
    def compact(row):
        return {k:v for k,v in row.items() if k not in ("inputs","build_context")}
    output=dict(seed, verifier_sha256=digest(Path(__file__).read_bytes()), selected_targets=args.targets or "all",
                required_final_theorems=sorted(n for m, ns in REQUIRED_BY_MODULE.items() if m in names for n in ns),
                compiled_originals={m:compact(done[m]) for m in sorted(missing)},
                modules={m:dict(compact(done[m]),**inventory[m]) for m in names},controls=controls(args,src,env,names))
    save(args.out,output)
    print("Verified",len(names),"experiment modules and",sum(x["declarations"] for x in inventory.values()),
          "local theorem/axiom declarations.",flush=True)


if __name__ == "__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    path_arg=lambda s:Path(s).resolve()
    for name in ("source","toolchain","mathlib","tower","slot","work","out"):
        ap.add_argument("--"+name,type=path_arg,required=True)
    ap.add_argument("--tower-manifest",type=path_arg,default=SLOT/"results/tower_build.json")
    ap.add_argument("--slot-manifest",type=path_arg,default=SLOT/"results/joint_check.json")
    ap.add_argument("--targets",nargs="+",help="Development subset; omit for the complete run.")
    run(ap.parse_args())
