"""Compile and kernel-replay the dyadic wave against the pinned Gaussian proof study."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
MODULES = ("EvenDescent", "OddSquares", "DyadicBase", "PrimitiveLift", "SquareDepth",
           "SingularGaussian", "GaussianDilates", "GaussianSharp")
AUDIT = ("oddRoots", "oddTail", "even_scaling", "lift_primitive",
         "primitive_mod_eight", "step_counts", "all_depths", "with_unit",
         "zero_tube_ratio", "zero_tube_measure", "singular_mass_zero", "late_tube", "fiber_mass",
         "realized_all", "sharp_floor", "sharp_witness")

def invoke(argv, work, env):
    proc = subprocess.run(list(map(str, argv)), cwd=work, env=env,
                          capture_output=True, text=True)
    output = proc.stdout + proc.stderr
    if proc.returncode or "sorryAx" in output or "declaration uses `sorry`" in output:
        raise RuntimeError(output)
    return output.strip()

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def verify(sdk, mathlib, predecessor, work, imports):
    prior = json.loads((predecessor / "manifest.json").read_text())
    if prior["original_commit"] != "40e56bab026552e089d7afcfeff08d2defb9c005":
        raise ValueError("Unexpected original source pin")
    packages = sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean"))
    paths = [work, *imports, mathlib / ".lake/build/lib/lean", *packages, sdk / "lib/lean"]
    env = dict(os.environ, LEAN_SYSROOT=str(sdk), LEAN_PATH=os.pathsep.join(map(str, paths)))
    toolchain = invoke([sdk / "bin/lean", "--version"], work, env)
    revision = invoke(["git", "rev-parse", "HEAD"], mathlib, env)
    if prior["lean"] not in toolchain or revision != prior["mathlib"]:
        raise ValueError("Unexpected Lean or Mathlib revision")
    for row in prior["modules"]:
        module_path = Path(*row["module"].split(".")).with_suffix(".lean")
        source = predecessor / row["path"]
        if digest(source) != row["sha256"]:
            raise ValueError(f"Source hash mismatch for {source}")
        if not imports:
            target = work / module_path
            target.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(source,target)
            flags = (["-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
                      "-DmaxSynthPendingDepth=3", "-DmaxHeartbeats=4000000",
                      "--tstack=400000"] if row["kind"]=="pinned" else [])
            invoke([sdk/"bin/lean","-j1",*flags,"-o",module_path.with_suffix(".olean"),
                    module_path],work,env)
    modules = []
    for module in MODULES:
        src = ROOT / (module + ".lean")
        shutil.copyfile(src,work/src.name)
        invoke([sdk/"bin/lean","-j1","-o",module+".olean",src.name],work,env)
        log = invoke([sdk/"bin/leanchecker","-v",module],work,env)
        if f"replaying {module}" not in log:
            raise ValueError(f"Missing replay for {module}")
        modules.append(dict(name=module,source_sha256=digest(src),replay=log))
    audit = work / "DyadicAudit.lean"
    audit.write_text("import GaussianSharp\n"+"".join(
        f"#print axioms DyadicWave.{name}\n" for name in AUDIT))
    axioms = invoke([sdk/"bin/lean",audit.name],work,env)
    for name in AUDIT:
        expected = f"'DyadicWave.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
        if expected not in axioms:
            raise ValueError(axioms)
    return dict(toolchain=toolchain,mathlib=revision,original_commit=prior["original_commit"],
                prior_manifest_sha256=digest(predecessor/"manifest.json"),
                predecessor_study="b4d12e0825d2191f38fdfb5e97b327c8c8ad1b3d",
                modules=modules,axioms=axioms)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sdk",type=Path,required=True)
    parser.add_argument("--mathlib",type=Path,required=True)
    parser.add_argument("--prior",type=Path,required=True,help="gaussian-target-four study from the pinned predecessor")
    parser.add_argument("--imports",type=Path,action="append",default=[],
                        help="Compiled predecessor roots, in Lean search order; otherwise rebuild all pinned prior modules")
    parser.add_argument("--receipt",type=Path,help="Write fresh JSON receipt instead of comparing with the bundled one")
    args=parser.parse_args()
    with tempfile.TemporaryDirectory() as temp:
        record=verify(args.sdk.resolve(),args.mathlib.resolve(),args.prior.resolve(),
                      Path(temp),[p.resolve() for p in args.imports])
    if args.receipt:
        args.receipt.write_text(json.dumps(record,indent=2)+"\n")
    elif record!=json.loads((ROOT/"receipt.json").read_text()):
        raise ValueError("Replay differs from published receipt")
    print(f"Kernel replay accepted {len(MODULES)} modules and audited {len(AUDIT)} declarations.")

if __name__=="__main__":
    main()
