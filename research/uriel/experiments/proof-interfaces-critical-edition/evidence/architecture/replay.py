"""Re-elaborate and kernel-replay the selected modules with existing pinned dependencies."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


PACKAGE = Path(__file__).resolve().parent
A = "Development.AutomorphicArithmetic."
OLD = [A + "DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow",
       A + "PrimitiveCosets.LevelFamily", A + "PrimitiveCosets.CoreGm",
       A + "PrimitiveCosets.Imports", A + "PrimitiveCosets.WindowInequalityOfArtinInputs",
       A + "PrimitiveCosets.LevelGmLeOnFamilyScales",
       "Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.TopWin",
       A + "CharacterBoxes.ZeroFreeAllOfTopG"]
NEW = ["Lib.Analytic.Landau", "New.Reduction.Zeros.PrimeError",
       "New.Reduction.Zeros.Criterion", "New.Reduction.PrimeSums",
       "New.Reduction.MainInequality", "New.Reduction.OneSidedBound"]
CHAR = A + "DedekindLFunctions.CharFamily"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked_command(args, **kw):
    result = subprocess.run(args, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, **kw)
    if result.returncode or "sorryAx" in result.stdout or "declaration uses `sorry`" in result.stdout:
        raise RuntimeError(result.stdout[-4000:] or f"{args[0]} failed: {result.returncode}")
    return result.stdout.strip()


def verify_source(edition, root, trace):
    for row in trace["declarations"][edition]:
        path = root / row["path"]
        raw = path.read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        if blob != row["git_blob"]:
            raise ValueError(f"Pinned source mismatch: {row['path']}")


def check_modules(work, sdk, libraries, sources, expected, receipt):
    # Lean resolves a package namespace at one search-path root. Overlay project objects
    # to let freshly compiled modules and their sibling imports share that namespace.
    work.mkdir()
    for path in libraries[0].rglob("*"):
        if path.is_file():
            dest = work / path.relative_to(libraries[0])
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.symlink_to(path)
    env = dict(os.environ, LEAN_SYSROOT=str(sdk),
               LEAN_PATH=os.pathsep.join(map(str, [work, *libraries, sdk / "lib/lean"])))
    for mod, src in sources:
        rel = Path(mod.replace(".", "/") + ".lean")
        if digest(src) != expected[mod]["source_sha256"]:
            raise ValueError(f"Source hash mismatch for {mod}")
        dest = work / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        for suffix in (".lean", ".olean", ".olean.private", ".olean.server", ".ilean", ".ir"):
            link = dest.with_suffix(suffix)
            if link.is_symlink():
                link.unlink()
        shutil.copyfile(src, dest)
        build = checked_command([sdk/"bin/lean", "-j1", "-o", rel.with_suffix(".olean"), rel],
                                cwd=work, env=env)
        checker = checked_command([sdk/"bin/leanchecker", "-v", mod], cwd=work, env=env)
        receipt[mod] = dict(source_sha256=digest(src), object_sha256=digest(dest.with_suffix(".olean")),
                            compiler_messages=build, kernel=checker)
        print("replayed", mod, flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for flag in ("old-source", "old-objects", "old-mathlib", "old-sdk", "readable", "new-sdk"):
        ap.add_argument("--"+flag, type=Path)
    ap.add_argument("--current-source", type=Path)
    ap.add_argument("--mode", choices=("all", "old", "new", "bridge"), default="all")
    ap.add_argument("--receipt", type=Path, help="Optionally write a new run receipt")
    args = ap.parse_args()
    groups = ("old","new","bridge") if args.mode == "all" else (args.mode,)
    required = set()
    if "old" in groups:
        required.update(("old_source", "old_objects", "old_mathlib", "old_sdk"))
    if "new" in groups or "bridge" in groups:
        required.update(("readable", "new_sdk"))
    if "bridge" in groups:
        required.add("old_source")
    for name in sorted(required):
        if getattr(args, name) is None:
            ap.error(f"--{name.replace('_', '-')} is required for --mode {args.mode}")
    old = args.old_source.resolve() if args.old_source else None
    new = args.readable.resolve() if args.readable else None
    trace = json.loads((PACKAGE/"source_trace.json").read_text())
    historical = json.loads((PACKAGE/"replay_receipt.json").read_text())
    if old:
        verify_source("original", old, trace)
    if new:
        verify_source("readable", new, trace)
    if args.current_source:
        verify_source("head", args.current_source.resolve(), trace)
    receipt = {}
    for edition in groups:
        is_old = edition == "old"
        sdk = (args.old_sdk if is_old else args.new_sdk).resolve()
        mathlib = args.old_mathlib.resolve() if is_old else new/".lake/packages/mathlib"
        version = checked_command([sdk/"bin/lean", "--version"])
        mathrev = checked_command(["git", "-C", mathlib, "rev-parse", "HEAD"])
        if historical["environments"][edition]["lean_commit"] not in version or mathrev != historical["environments"][edition]["mathlib"]:
            raise ValueError(f"Unexpected toolchain or Mathlib for {edition}")
        objects = args.old_objects.resolve() if is_old else new/".lake/build/lib/lean"
        packages = mathlib/".lake/packages" if is_old else new/".lake/packages"
        libraries = [objects, mathlib/".lake/build/lib/lean", *sorted(packages.glob("*/.lake/build/lib/lean"))]
        if not objects.is_dir():
            raise ValueError(f"Missing built project libraries: {objects}")
        src = old if is_old else new
        mods = OLD if is_old else NEW
        if edition == "bridge":
            sources = [(CHAR, old/"src"/(CHAR.replace(".","/")+".lean")),
                       ("Euler", PACKAGE/"Euler.lean"), ("ObservableBridge", PACKAGE/"ObservableBridge.lean")]
        else:
            sources = [(mod, src/"src"/(mod.replace(".","/")+".lean")) for mod in mods]
        receipt[edition] = {}
        with tempfile.TemporaryDirectory() as temp:
            check_modules(Path(temp)/edition, sdk, libraries, sources,
                          historical["modules"][edition], receipt[edition])
    if args.receipt:
        args.receipt.write_text(json.dumps(receipt, indent=2)+"\n")


if __name__ == "__main__":
    main()
