"""Repeat the exact finite checks, and optionally replay the original or valuation certificate."""

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def replay_valuation(root, sdk):
    source = root / "ValuationLedger.lean"
    version = subprocess.check_output([sdk / "bin/lean", "--version"], text=True).strip()
    if "819816b2e0a3" not in version:
        raise ValueError("Unexpected Lean revision")
    result = dict(compiler=version, source_sha256=digest(source), commands=[])
    with tempfile.TemporaryDirectory() as temp:
        shutil.copyfile(source, Path(temp) / source.name)
        env = dict(os.environ, LEAN_SYSROOT=str(sdk), LEAN_PATH=temp)
        for cmd in (["lean","-j1","-o","ValuationLedger.olean",source.name],
                    ["leanchecker","-v","ValuationLedger"]):
            run = subprocess.run([sdk / "bin" / cmd[0], *cmd[1:]], cwd=temp, env=env,
                                 text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if run.returncode or "sorryAx" in run.stdout:
                raise ValueError(run.stdout)
            result["commands"].append(dict(command=cmd, exit=run.returncode, output=run.stdout.strip()))
    expected = json.loads((root / "valuation_replay.json").read_text())
    if result != expected:
        raise ValueError("Valuation module, axiom queries or checker output differ from the release")
    return result


def main():
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--lean", action="store_true")
    mode.add_argument("--valuation-lean", action="store_true")
    parser.add_argument("--sdk", type=Path, default=Path("/private/tmp/lean-4.33.1-darwin_aarch64"))
    parser.add_argument("--mathlib", type=Path, default=Path("/private/tmp/uriel-rh-mathlib4331"))
    parser.add_argument("--study", type=Path, default=Path("/private/tmp/nous-ramdilates/fresh"))
    parser.add_argument("--objects", type=Path, default=Path("/private/tmp/nous-uncapped/restored/obj"))
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    fresh = json.loads(subprocess.check_output([sys.executable, "-B", root / "finite_checks.py"]))
    if fresh != json.loads((root / "finite_results.json").read_text()):
        raise ValueError("Finite counts differ from the archived values")
    certificate = json.loads(subprocess.check_output([sys.executable, "-B", root / "digit_certificate.py"]))
    if certificate != json.loads((root / "digit_certificate.json").read_text()):
        raise ValueError("Digit character sums differ from the archived values")
    center = next(row for row in fresh["balls"] if row["depth"] == 6)
    if certificate["children"] != [center["count"], center["companion_count"]]:
        raise ValueError("The independent depth-six computations disagree")
    census = json.loads(subprocess.check_output([sys.executable, "-B", root / "valuation_census.py"]))
    if census != json.loads((root / "valuation_counts.json").read_text()):
        raise ValueError("Valuation census differs from the published counts")
    print("All 18 entries agree at uniformizer depths 8, 9 and 10.")
    if args.valuation_lean:
        ledger = replay_valuation(root, args.sdk.resolve())
        if args.receipt:
            args.receipt.write_text(json.dumps(ledger, indent=2) + "\n")
        print("Kernel replayed the primitive finite census and exact table scaling.")
        return
    if not args.lean:
        print("Seven exact six-square censuses and nine split-map controls agree. The independent character certificate matches both children.")
        return
    sdk, mathlib = args.sdk.resolve(), args.mathlib.resolve()
    version = subprocess.check_output([sdk / "bin/lean", "--version"], text=True).strip()
    lib_pin = subprocess.check_output(["git", "-C", mathlib, "rev-parse", "HEAD"], text=True).strip()
    if "819816b2e0a3" not in version or lib_pin != "0df444a360eaa60ab8c11dca51a86af692955474":
        raise ValueError("Unexpected Lean or Mathlib revision")
    source = root / "TargetFourHaar.lean"
    wanted = set(re.findall(r"^#print axioms (TargetFourHaar\.\w+)", source.read_text(), re.M))
    receipt = dict(compiler=version, mathlib=lib_pin, source_sha256=digest(source),
                   direct_study_objects={p:digest(args.study / (p + ".olean"))
                                         for p in ("DilateStableOddAll", "DilateEndpoint")},
                   counts_sha256=digest(root / "finite_results.json"), commands=[])
    with tempfile.TemporaryDirectory() as temp:
        work = Path(temp)
        shutil.copyfile(source, work / source.name)
        paths = [work, args.study.resolve(), args.objects.resolve(), mathlib / ".lake/build/lib/lean",
                 *sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean")), sdk / "lib/lean"]
        env = dict(os.environ, LEAN_SYSROOT=str(sdk), LEAN_PATH=os.pathsep.join(map(str, paths)))
        for cmd in (["lean", "-j1", "-o", "TargetFourHaar.olean", source.name],
                    ["leanchecker", "-v", "TargetFourHaar"]):
            run = subprocess.run([sdk / "bin" / cmd[0], *cmd[1:]], cwd=work, env=env,
                                 text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if run.returncode:
                raise SystemExit(run.stdout)
            if cmd[0] == "lean":
                pairs = re.findall(r"'(TargetFourHaar\.\w+)' depends on axioms: \[([^\]]*)\]", run.stdout)
                if {n for n, _ in pairs} != wanted or not wanted:
                    raise ValueError("Missing explicit axiom query")
                if any(set(v.split(", ")) - {"propext", "Classical.choice", "Quot.sound"} for _, v in pairs):
                    raise ValueError("Unexpected axiom")
                receipt["queries"] = len(pairs)
            receipt["commands"].append(dict(command=cmd, exit=run.returncode, output=run.stdout.strip()))
    text = json.dumps(receipt, indent=2) + "\n"
    if args.receipt:
        args.receipt.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
