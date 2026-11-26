"""Replay the selected-place proofs in the two pinned Lean environments."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "prior"))
from prior.replay import digest, run, TOOLCHAINS

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def resolve_checkout(args, trace):
    source_root = (args.original if args.mode == "original" else args.readable)
    if source_root is None:
        raise ValueError(f"Supply the {args.mode} source checkout.")
    source_root = source_root.resolve()
    for row in trace[args.mode]["files"]:
        if digest(source_root / row["path"]) != row["sha256"]:
            raise ValueError(f"Pinned source mismatch: {row['path']}")
    if args.mode == "readable":
        mathlib = source_root / ".lake/packages/mathlib"
        libs = [source_root / ".lake/build/lib/lean",
                *sorted((source_root / ".lake/packages").glob("*/.lake/build/lib/lean"))]
    else:
        if args.old_mathlib is None or args.old_objects is None:
            raise ValueError("Supply the built original library and the original Mathlib checkout.")
        mathlib = args.old_mathlib.resolve()
        libs = [args.old_objects.resolve(), mathlib / ".lake/build/lib/lean",
                *sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean"))]
    return source_root, mathlib, libs


def checked_run(source, work, sdk, libs):
    result = run(source, source.stem, work, sdk, libs)
    names = set(re.findall(r"^#print axioms ([^\s]+)", source.read_text(), re.M))
    queries = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", result["elaboration"]))
    # Open Classical shortens the printed name of Classical.choice to choice.
    dependencies = [{("Classical.choice" if axiom == "choice" else axiom)
                     for axiom in printed.split(", ") if axiom}
                    for printed in queries.values()]
    if set(queries) != names or any(deps - ALLOWED for deps in dependencies):
        raise ValueError(f"Unexpected axiom output for {source.name}.")
    if result["kernel"] != f"replaying {source.stem}":
        raise ValueError(f"Unexpected kernel output for {source.name}.")
    return result


def prepare_prior(args, work, sdk, libs):
    previous = ROOT / "prior"
    modules = ("WitnessInterface", "ReadableDatum", "ScaleControl", "HostComparison", "RecoveryCriteria")
    historical = json.loads((previous / "replay_receipt.json").read_text())
    hashes = {m["module"]: m["object_sha256"] for r in historical["runs"] for m in r["modules"]}
    if args.prior_objects:
        directory = args.prior_objects.resolve()
        for module in modules:
            if digest(directory / (module + ".olean")) != hashes[module]:
                raise ValueError(f"Prior compiled module differs: {module}")
        return [directory, *libs], []
    results = [checked_run(previous / (module + ".lean"), work, sdk, libs) for module in modules]
    return libs, results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("original", "readable"))
    for flag in ("sdk", "original", "readable", "old-objects", "old-mathlib", "prior-objects", "receipt"):
        parser.add_argument("--" + flag, type=Path, required=flag == "sdk")
    args = parser.parse_args()
    trace = json.loads((ROOT / "source_trace.json").read_text())
    for f, expected in trace["prior"]["files"].items():
        if digest(ROOT / "prior" / f) != expected:
            raise ValueError(f"Inherited proof mismatch: {f}")
    sdk = args.sdk.resolve()
    _, mathlib, libraries = resolve_checkout(args, trace)
    version = subprocess.check_output([sdk / "bin/lean", "--version"], text=True).strip()
    mathrev = subprocess.check_output(["git", "-C", mathlib, "rev-parse", "HEAD"], text=True).strip()
    lean_pin, mathlib_pin = TOOLCHAINS[args.mode]
    if lean_pin not in version or mathrev != mathlib_pin:
        raise ValueError("Unexpected Lean or Mathlib revision.")
    with tempfile.TemporaryDirectory() as temp:
        work = Path(temp)
        if args.mode == "readable":
            libraries, inherited = prepare_prior(args, work, sdk, libraries)
            modules = ("ReadableCapacity", "SameSet")
        else:
            inherited = []
            modules = ("OriginalCapacity",)
        current = [checked_run(ROOT / (mod + ".lean"), work, sdk, libraries) for mod in modules]
    result = dict(compiler=version, mathlib=mathrev, source_pin=trace[args.mode]["commit"],
                  inherited_compiled_modules=inherited,
                  used_previous_objects=bool(args.prior_objects),
                  experiment_modules=current)
    data = json.dumps(result, indent=2) + "\n"
    if args.receipt:
        args.receipt.write_text(data)
    else:
        print(data, end="")


if __name__ == "__main__":
    main()
