"""Compile the new local theorems against authenticated original modules and audit proof terms."""
import argparse
from graphlib import TopologicalSorter
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

from build_original import FLAGS, HERE, PIN, closure, dump, environment, pinned_source, pinned_tree, relative

LOCAL = ("SameIndex", "Enriched", "OriginalDesign", "JointControls", "TermAudit")
GOOD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


def run(args):
    tc, base, bridges, work = (getattr(args,n).resolve() for n in ("toolchain","base","bridges","work"))
    src, lib = work/"src", work/"lib"
    src.mkdir(parents=True,exist_ok=True)
    lib.mkdir(exist_ok=True)
    tree = pinned_tree()
    imports = set()
    for name in LOCAL:
        data = (HERE/(name+".lean")).read_bytes()
        (src/(name+".lean")).write_bytes(data)
        imports.update(mod for mod in re.findall(r"(?m)^import (\S+)",data.decode()) if mod not in LOCAL and not mod.startswith("Lean."))
    graph = closure(imports,args.source,tree,src)
    env, version = environment(tc,args.mathlib.resolve())
    env["LEAN_PATH"] = os.pathsep.join([str(lib),env["LEAN_PATH"]])
    report = dict(pin=PIN, toolchain=version, local={}, additional_original={}, controls={})
    verified = set()
    # The two compilation stages authenticate every source to Git when generating these records.
    for cache,filename in ((base,"original_build.json"),(bridges,"bridge_build.json")):
        record = json.loads((args.out/filename).read_text())
        if record["pin"] != PIN or record["toolchain"] != version:
            raise ValueError("Prior build provenance differs")
        for name,row in record["modules"].items():
            if name not in graph:
                continue
            blob = (cache/"lib"/relative(name,".olean")).read_bytes()
            if sha256(blob).hexdigest() != row["olean_sha256"] or row["source_blob"]!=tree["src/"+relative(name,".lean").as_posix()]:
                raise ValueError("Unauthenticated cached module "+name)
            dest = lib/relative(name,".olean")
            dest.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(cache/"lib"/relative(name,".olean"), dest)
            verified.add(name)
    def compile_one(name):
        f = relative(name,".lean")
        out = lib/relative(name,".olean")
        out.parent.mkdir(parents=True,exist_ok=True)
        p = subprocess.run([tc/"bin/lean",*FLAGS,"--root=.","-o",out,f],env=env,cwd=src,capture_output=True,text=True)
        log = (p.stdout+p.stderr).strip()
        if p.returncode or "declaration uses 'sorry'" in log:
            raise RuntimeError(name+"\n"+log)
        return {"source_sha256":sha256((src/f).read_bytes()).hexdigest(),"olean_sha256":sha256(out.read_bytes()).hexdigest()},log
    for name in TopologicalSorter(graph).static_order():
        if name not in verified:
            row,_ = compile_one(name)
            report["additional_original"][name] = row
    path = "src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/CountsIrreducibilityConstants.lean"
    block = b"".join(pinned_source(path,args.source,tree).splitlines(keepends=True)[31:35])
    if sha256(block).hexdigest()!="53cd715de9f0e60d9df6104b54cb30fb9600034bf61ee6dcce308681f79ea10a" or (src/"OriginalDesign.lean").read_bytes().count(block)!=1:
        raise ValueError("Design class excerpt differs from original")
    report["abbrev_excerpt_sha256"] = sha256(block).hexdigest()
    for name in LOCAL:
        row,log = compile_one(name)
        p = subprocess.run([tc/"bin/leanchecker","-v",name],cwd=src,env=env,capture_output=True,text=True)
        if p.returncode or (p.stdout+p.stderr).strip() != "replaying "+name:
            raise RuntimeError(p.stdout+p.stderr)
        row["replay"] = (p.stdout+p.stderr).strip()
        report["local"][name] = row
        if name=="TermAudit":
            terms=[json.loads(l.removeprefix("JOINT_TERM ")) for l in log.splitlines() if l.startswith("JOINT_TERM ")]
            by_name = {t["name"]: t for t in terms}
            if len(terms)!=17 or len(by_name)!=17 or any(set(t["axioms"])-GOOD_AXIOMS for t in terms):
                raise ValueError("Proof or axiom inventory differs")
            conclusion = by_name["UrielJoint.joint_of_original_character_design"]
            expected_calls = {"UpperTheory.Top.originalDesign_with_qdRows", "UpperTheory.Top.hypV_of_cls",
                              "UrielJoint.joint_of_design"}
            if not expected_calls.issubset(conclusion["proof"]):
                raise ValueError("Combined proof is missing a direct design, cohomology or joint-witness reference")
            dump(args.out/"proof_terms.json",terms)
    header = """import Enriched
open UpperTheory.Top Formalism.HC Formalism.MainNotions
"""
    first = """example {eps la x : ℝ} (F : FamP eps) (ψ : PChar) (h : (GChi ψ).cls la F)
    (hx : F.x1 < x) (i j : F.Ix x) :
    VVle (F.D x i).host.E (F.D x i).R.t (Real.sqrt (F.L x i).sc.b) := (h.2 x hx INDEX).2
"""
    second = """example {eps J c x Y : ℝ} {q d e : ℕ} (ψ : PChar) (h : WinDatum ψ eps J c x Y q d e)
    (E : Type) [Field E] [NumberField E] (hf : IsChiField ψ e PAIR E) :
    VVle E ⌊x ^ (400 : ℝ)⌋₊ (Real.sqrt (Real.exp (x ^ eps))) := h.bound E hf
"""
    for label,body,accept in (("index_matched",first.replace("INDEX","i"),True),
                              ("index_changed",first.replace("INDEX","j"),False),
                              ("pair_matched",second.replace("PAIR","q d"),True),
                              ("pair_reversed",second.replace("PAIR","d q"),False)):
        path = src/"BindingControl.lean"
        path.write_text(header+body)
        p = subprocess.run([tc/"bin/lean",*FLAGS,path.name],cwd=src,env=env,capture_output=True,text=True)
        log=(p.stdout+p.stderr).strip()
        if (p.returncode==0)!=accept or (not accept and "type mismatch" not in log.lower()):
            raise RuntimeError(label+"\n"+log)
        report["controls"][label]=dict(exit=p.returncode,output=log)
    dump(args.out/"join_checks.json",report)
    print("Verified joint declarations, 17 term inventories and four binding controls.")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for key in ("source","toolchain","mathlib","base","bridges","work","out"):
        parser.add_argument("--"+key,type=Path,required=True)
    run(parser.parse_args())


if __name__=="__main__":
    main()
