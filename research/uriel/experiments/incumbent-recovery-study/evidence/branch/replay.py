"""Replay the new source-connected endpoints and their preceding gain supplement."""
import argparse
from graphlib import TopologicalSorter
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryDirectory


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("helpers", "original", "mathlib", "toolchain", "retained-library",
                 "retained-record", "prior-gain"):
        parser.add_argument("--" + name, required=True, type=lambda v: Path(v).resolve())
    parser.add_argument("--staged",type=lambda v: Path(v).resolve(),
                        help="optional original objects rebuilt in the prior gain run")
    args = parser.parse_args()
    sys.path.insert(0,str(args.helpers))
    from build_original import FLAGS, PIN, closure, environment, pinned_tree, relative

    prior_hash = "55d1d8c1db27c9f61cea6bebcfd836ea1fb3d13a331e146699f19d6b15ac2bfc"
    prior_record = json.loads((args.prior_gain/"verification.json").read_bytes())
    prior_src = args.prior_gain / "ActualGain.lean"
    if digest(prior_src) != prior_hash or prior_record["supplement_sha256"] != prior_hash:
        raise ValueError("Prior supplement differs from the study's research pin.")
    fit = json.loads(args.retained_record.read_bytes())
    tree = pinned_tree()
    env, version = environment(args.toolchain,args.mathlib)
    if [PIN,FLAGS,version] != [fit["pin"],fit["flags"],fit["toolchain"]]:
        raise ValueError("Retained objects and toolchain metadata differ.")
    recorded = fit["source_closure"]
    inventory = {}
    for name in closure(recorded["direct_original_imports"],args.original,tree):
        f = relative(name,".lean")
        inventory[name] = [tree["src/"+f.as_posix()],digest(args.retained_library/relative(name,".olean"))]
    invhash = sha256((json.dumps(inventory,sort_keys=True,indent=2)+"\n").encode()).hexdigest()
    if invhash != prior_record["inventory_sha256"] or invhash != recorded["source_blob_and_object_inventory_sha256"]:
        raise ValueError("Retained library failed authentication.")
    target = "Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PartnerCountOfCentral"
    graph = closure([target],args.original,tree)
    names = ["hole_cap","no_successor_credit","no_successor_direct_lower",
             "recovery_lower","recovery_eq_price_sub_credit"]
    with TemporaryDirectory() as scratch:
        work = Path(scratch)
        env["LEAN_PATH"] = str(work)+os.pathsep+env["LEAN_PATH"]
        lean, kernel = [args.toolchain/"bin"/s for s in ("lean","leanchecker")]

        def run(argv):
            proc = subprocess.run(argv,cwd=work,env=env,capture_output=True,text=True)
            out = (proc.stdout+proc.stderr).strip()
            if proc.returncode or "sorryAx" in out or "declaration uses 'sorry'" in out:
                raise RuntimeError(out)
            return out

        verified = {}
        for name in TopologicalSorter(graph).static_order():
            f, obj = [relative(name,s) for s in (".lean",".olean")]
            (work/obj).parent.mkdir(parents=True,exist_ok=True)
            if name in inventory:
                (work/obj).symlink_to(args.retained_library/obj)
                continue
            (work/f).write_bytes((args.original/"src"/f).read_bytes())
            if args.staged:
                recorded_hash = prior_record["original_modules_rebuilt"][name]["olean_sha256"]
                if digest(args.staged/obj) != recorded_hash:
                    raise ValueError("Staged object differs from the previous replay: "+name)
                (work/obj).write_bytes((args.staged/obj).read_bytes())
            else:
                run([lean,*FLAGS,"--root=.","-o",obj,f])
            checked = run([kernel,"-v",name])
            if checked != "replaying "+name:
                raise ValueError(checked)
            verified[name] = {"git_blob":tree["src/"+f.as_posix()],"object_sha256":digest(work/obj),"kernel":checked}

        results = {}
        new_source = Path(__file__).resolve().with_name("IncumbentRecovery.lean")
        for path in (prior_src,new_source):
            name = path.stem
            (work/path.name).write_bytes(path.read_bytes())
            log = run([lean,*FLAGS,"--root=.","-o",name+".olean",path.name])
            axioms = re.sub(r"\n[ \t]+"," ",log).splitlines()
            expected = prior_record["elaboration"] if name=="ActualGain" else [
                "'Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit."+n+
                "' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names]
            if set(axioms)!=set(expected) or len(axioms)!=len(expected):
                raise ValueError(log)
            checked = run([kernel,"-v",name])
            if checked != "replaying "+name:
                raise ValueError(checked)
            results[name] = dict(source_sha256=digest(path),object_sha256=digest(work/(name+".olean")),
                                 kernel=checked,axioms=sorted(axioms))
        receipt = dict(pin=PIN,toolchain=version,authenticated_inventory=len(inventory),
                       inventory_sha256=invhash,original_modules_in_closure=len(graph),
                       original_rebuilt_verified=verified,modules=results)
    print(json.dumps(receipt,indent=2))


if __name__=="__main__":
    main()
