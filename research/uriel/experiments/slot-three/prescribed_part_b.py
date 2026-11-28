"""Verify the explicit exception selector against the pinned odd-prime Part B."""
import argparse
from difflib import SequenceMatcher, unified_diff
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
JOINT = HERE.parent/"joint-witness"
sys.path.insert(0, str(JOINT))
from build_original import FLAGS, PIN, closure, dump, environment, pinned_source, pinned_tree, relative

ORIGINAL = "Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.PartB"
PATH = "src/"+relative(ORIGINAL, ".lean").as_posix()
MODULE = "PrescribedPartB"
BEFORE = "UpperTheory.V.Win.partB"
AFTER = "SlotThree.partB_prescribed"


def check(args):
    tc, work, cache = args.toolchain.resolve(), args.work.resolve(), args.cache.resolve()
    work.mkdir(parents=True, exist_ok=True)
    env, versions = environment(tc, args.mathlib.resolve())
    tree = pinned_tree()
    graph = closure([ORIGINAL], args.source.resolve(), tree)
    manifest = {}
    records = [args.manifest] if args.manifest else [
        JOINT/"results"/name for name in ("original_build.json", "bridge_build.json")]
    for path in records:
        record = json.loads(path.read_bytes())
        if record["pin"] != PIN or record["toolchain"] != versions:
            raise ValueError(f"Source or compiler differs in {path}")
        manifest.update(record["modules"])
    missing = sorted(graph.keys() - manifest.keys())
    if missing:
        raise ValueError(f"Missing original modules in manifest ({len(missing)}). First: {missing[0]}")
    digest = sha256()
    for name in sorted(graph):
        src_id = tree["src/"+relative(name,".lean").as_posix()]
        binary = sha256((cache/relative(name,".olean")).read_bytes()).hexdigest()
        if manifest[name]["source_blob"] != src_id or manifest[name]["olean_sha256"] != binary:
            raise ValueError("Unexpected source/object pair: "+name)
        digest.update((name+" "+src_id+" "+binary+"\n").encode())

    # Keep the local search root empty of imported project objects. All project
    # dependencies then resolve under the authenticated single namespace root.
    if any((work/top).exists() for top in {n.split(".")[0] for n in graph}):
        raise ValueError("Use a dedicated work directory for this run")
    env["LEAN_PATH"] = os.pathsep.join((str(work),str(cache),env["LEAN_PATH"]))
    before = pinned_source(PATH, args.source.resolve(), tree).decode().splitlines(keepends=True)
    data = (HERE/(MODULE+".lean")).read_bytes()
    after = data.decode().splitlines(keepends=True)
    original_range_changes = []
    matched = 0
    for op,a,b,c,d in SequenceMatcher(a=before,b=after,autojunk=False).get_opcodes():
        if op == "equal":
            matched += b-a
        else:
            original_range_changes.append([op,a,b,c,d])
    # Require the recorded edit locations. Intervals are zero-based, half-open.
    if [(tag,a,b) for tag,a,b,_,_ in original_range_changes] != [
        ("replace",49,50),("insert",52,52),("replace",53,54),("replace",57,58),
        ("delete",61,62),("replace",73,75),("insert",95,95)]:
        raise ValueError("Unexpected source differences: "+repr(original_range_changes))

    def run(command):
        p = subprocess.run(command, cwd=work, env=env, capture_output=True, text=True)
        output = (p.stdout+p.stderr).strip()
        if p.returncode or "declaration uses 'sorry'" in output or "sorryAx" in output:
            raise RuntimeError(output)
        return output

    (work/(MODULE+".lean")).write_bytes(data)
    obj = work/(MODULE+".olean")
    compiler = run([tc/"bin/lean",*FLAGS,"--root=.","-o",obj,MODULE+".lean"])
    m = re.search(r"'SlotThree\.partB_prescribed' depends on axioms: \[([^\]]*)\]", compiler)
    if not m or set(m.group(1).split(", ")) != {"propext","Classical.choice","Quot.sound"}:
        raise ValueError(compiler)
    replays = {}
    for name in (ORIGINAL,MODULE):
        replays[name] = run([tc/"bin/leanchecker","-v",name])
        if replays[name] != "replaying "+name:
            raise ValueError(replays[name])
    audit = f'''import {ORIGINAL}
import {MODULE}
import Lean.Util.FoldConsts
open Lean Elab Command
run_cmd do
  for decl in ["{BEFORE}", "{AFTER}"] do
    let n := decl.toName
    let ci ← getConstInfo n
    let some val := ci.value? (allowOpaque := true) | throwError "could not access proof"
    let names := (val.getUsedConstants.map Name.toString).qsort (· < ·)
    IO.println ("EDGES " ++ (toJson names).compress)

open UpperTheory.V.Win

theorem SlotThree.recover_partB_type : type_of% UpperTheory.V.Win.partB := by
  classical
  intro CK hCK hK l R _ hl A hA L _ _ hL hAB J Ct eps A1 hJ hCt heps
  obtain ⟨c, _, pick⟩ := exc l R L hAB
  choose E hE using pick
  obtain ⟨x0, h⟩ := SlotThree.partB_prescribed CK hCK hK l R hl A hA L hL hAB c E hE J Ct eps A1 hJ hCt heps
  refine ⟨x0, fun e t hAdm X => ?_⟩
  obtain ⟨S, _, hcard, estimate⟩ := h e t hAdm X
  exact ⟨S, hcard, estimate⟩

#print axioms SlotThree.recover_partB_type
'''
    (work/"AuditPartB.lean").write_text(audit)
    log = run([tc/"bin/lean",*FLAGS,"AuditPartB.lean"])
    edges = [set(json.loads(line[6:])) for line in log.splitlines() if line.startswith("EDGES ")]
    needed = {"point2","final","layerex","layeriso","abiso","vvat","shaInv_congr"}
    if len(edges)!=2 or any(needed-{n.split(".")[-1] for n in e} for e in edges):
        raise ValueError("Required original analytical dependency missing")
    exc = "UpperTheory.V.Win.exc"
    if exc not in edges[0] or exc in edges[1] or BEFORE in edges[1]:
        raise ValueError("Elaborated proofs did not separate the supplied selector")
    projected = re.search(r"'SlotThree\.recover_partB_type' depends on axioms: \[([^\]]*)\]", log)
    if not projected or set(projected.group(1).split(", ")) != {"propext","Classical.choice","Quot.sound"}:
        raise ValueError(log)
    dump(args.out,dict(pin=PIN, toolchain=versions, flags=FLAGS, original_module=ORIGINAL,
        original_source_blob=tree[PATH], closure_count=len(graph), source_object_manifest_sha256=digest.hexdigest(),
        source_sha256=sha256(data).hexdigest(), olean_sha256=sha256(obj.read_bytes()).hexdigest(),
        original_lines=len(before), retained_original_lines=matched, original_edit_intervals=original_range_changes,
        diff="".join(unified_diff(before,after,fromfile="pinned/PartB.lean",tofile=MODULE+".lean")),
        compiler_output=compiler, replays=replays, recovery_at_exact_published_type=projected.group(0),
        shared_direct_calls=sorted(
            n for n in edges[0]&edges[1] if n.split(".")[-1] in needed),
        exc_direct_call={BEFORE:True, AFTER:False}))
    print(f"Authenticated {len(graph)} original modules; replayed PartB and {MODULE}. "
          f"Retained {matched}/{len(before)} source lines.")


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    for name in ("toolchain","source","mathlib","work","cache","out"):
        p.add_argument("--"+name, type=Path, required=True)
    p.add_argument("--manifest", type=Path,
                   help="Single source/object manifest covering PartB, such as the tower_build.json for --cache")
    check(p.parse_args())
