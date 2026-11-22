"""Replay the concrete field experiment and compare elaborated dependencies and rejected controls."""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess

from build_tower import FLAGS, HERE, PIN, closure, dump, environment, pinned_tree, relative

MODULES = ("BaseField", "SlotThree", "FieldModel", "CyclotomicTransport", "RankZero", "PrescribedPartB",
           "ZeroLift", "SlotApplication", "ProofAudit")
STANDARD = {"propext", "Quot.sound", "Classical.choice"}
EDGES = {
    "standard_common_lift": ["SlotThree.CyclotomicTransport.all_layers_iff", "SlotThree.common_lift"],
    "CyclotomicTransport.all_layers_iff": ["SlotThree.CyclotomicTransport.class_card"],
    "tower_module_zero": ["UpperTheory.V.Two.levelRk", "UpperTheory.V.Two.infRk", "UpperTheory.V.Two.genOfRk"],
    "layer_zero": ["SlotThree.tower_module_zero", "UpperTheory.V.PropA.genLevel", "UpperTheory.V.PropA.descends"],
    "any_center": ["SlotThree.layer_zero"],
    "certified_opposite": ["SlotThree.any_center", "SlotThree.firstBound_of_card",
                            "SlotThree.zero_weights", "SlotThree.singleton_weights"],
    "common_lift": ["SlotThree.tower_module_zero", "SlotThree.same_lift_opposite", "SlotThree.certified_one"],
    "partB_for_center": ["SlotThree.partB_prescribed", "SlotThree.FieldModel.fieldModel",
                         "SlotThree.actualABound", "SlotThree.firstBound_of_card"],
}


def run(args):
    env, version = environment(args.toolchain, args.mathlib)
    record = json.loads((args.out / "tower_build.json").read_bytes())
    if record["pin"] != PIN or record["toolchain"] != version:
        raise ValueError("Source or toolchain differs from tower build")
    tree = pinned_tree()
    imports = set()
    for name in MODULES:
        source = (HERE / (name + ".lean")).read_text()
        imports.update(m for m in re.findall(r"(?m)^import (\S+)", source) if m not in MODULES
                       and not m.startswith(("Mathlib", "Lean.")))
    graph = closure(imports, args.source, tree)
    for name in graph:
        row = record["modules"][name]
        path = args.tower / "lib" / relative(name,".olean")
        if row["source_blob"] != tree["src/"+relative(name,".lean").as_posix()] or sha256(path.read_bytes()).hexdigest()!=row["olean_sha256"]:
            raise ValueError("Unauthenticated original dependency " + name)
    src, lib = args.work / "src", args.work / "lib"
    src.mkdir(parents=True,exist_ok=True)
    lib.mkdir(exist_ok=True)
    env["LEAN_PATH"] = os.pathsep.join([str(lib), str(args.tower / "lib"), env["LEAN_PATH"]])
    def invoke(argv, reject=False):
        p = subprocess.run(argv,cwd=src,env=env,capture_output=True,text=True)
        message = (p.stdout+p.stderr).strip()
        if reject:
            if not p.returncode or "type mismatch" not in message.lower():
                raise RuntimeError(message)
        elif p.returncode or "sorryAx" in message or "declaration uses 'sorry'" in message:
            raise RuntimeError(message)
        return message
    report = dict(pin=PIN, toolchain=version, flags=FLAGS, authenticated_imports=len(graph), modules={}, controls={})
    for name in MODULES:
        data = (HERE/(name+".lean")).read_bytes()
        (src/(name+".lean")).write_bytes(data)
        obj = lib/(name+".olean")
        cmd=[args.toolchain/"bin/lean",*FLAGS,"--root=.","-o",obj,name+".lean"]
        log=invoke(cmd)
        replay=invoke([args.toolchain/"bin/leanchecker","-v",name])
        if replay != "replaying "+name:
            raise ValueError(replay)
        report["modules"][name] = dict(source_sha256=sha256(data).hexdigest(),olean_sha256=sha256(obj.read_bytes()).hexdigest(),
                                       replay=replay)
        print(replay,flush=True)
        if name == "ProofAudit":
            audit=[json.loads(l.removeprefix("SLOT3_AUDIT ")) for l in log.splitlines() if l.startswith("SLOT3_AUDIT ")]
            index={r["name"]:r for r in audit}
            if len(audit)!=19 or len(index)!=19 or any(set(row["axioms"])-STANDARD for row in audit):
                raise ValueError("Unexpected declaration or axiom list")
            for short,names in EDGES.items():
                if set(names) - set(index["SlotThree."+short]["body"]):
                    raise ValueError("Expected dependency missing in " + short)
            if "SlotThree.TowerClassHyp" not in index["SlotThree.certified_one"]["type"]:
                raise ValueError("All-layer assumption missing from target signature")
            dump(args.out/"proof_terms.json",audit)
    controls = {
      "base_only": "example : SlotThree.TowerClassHyp := SlotThree.BaseField.three_not_dvd_class_card",
      "anonymous_set": """open UpperTheory.V.Win
example (S : Finset ℕ) (h : FirstBound 3 1 1 SlotThree.L 64 S) : 1 ∈ S := h""",
    }
    for label,body in controls.items():
        (src/"Rejected.lean").write_text("import SlotApplication\n"+body+"\n")
        report["controls"][label] = invoke([args.toolchain/"bin/lean",*FLAGS,"Rejected.lean"],reject=True)
    dump(args.out/"joint_check.json",report)


if __name__ == "__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ("source","toolchain","mathlib","work","out","tower"):
        ap.add_argument("--"+name,type=lambda s:Path(s).resolve(),required=True)
    run(ap.parse_args())
