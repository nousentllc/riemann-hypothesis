"""Authenticate source spans and kernel-check the original Fourier-cell matrix lemma."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time


PIN = "40e56bab026552e089d7afcfeff08d2defb9c005"
MODULE = ("Development.WeilBound.CoreStatements.AutomorphicKernels."
          "SiegelWeilFormula.UnfoldingCompactness.ExistsBetaPf")
THEOREM = "PositivityTheory.SiegelWeilFormula.kunf.exists_beta_pf"


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args], text=True).strip()


def authenticate(source, repo):
    ledger_path = Path(__file__).resolve().parent.parent / "source_trace.json"
    ledger = json.loads(ledger_path.read_text())
    if ledger["commit"] != PIN:
        raise ValueError("Unexpected original-source commit")
    files = [item for item in ledger["files"] if "orbit-cell" in item["groups"]]
    if not files:
        raise ValueError("The source ledger contains no orbit-cell files")
    for item in files:
        path = item["path"]
        raw = (source / path).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        digest = hashlib.sha256(raw).hexdigest()
        line_count = len(raw.splitlines())
        if not (blob == item["git_blob"] == git(repo, "rev-parse", f"{PIN}:{path}")
                and digest == item["sha256"]
                and all(1 <= first <= last <= line_count for first, last in item["spans"])):
            raise ValueError(f"Source verification failed for {path}")
    return files


def run(source, repo, sdk, mathlib):
    files = authenticate(source, repo)
    manifest = json.loads(git(repo, "show", f"{PIN}:lake-manifest.json"))
    math_pin = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
    if git(mathlib, "rev-parse", "HEAD") != math_pin:
        raise ValueError(f"Expected Mathlib {math_pin}")
    lean_version = git(repo, "show", f"{PIN}:lean-toolchain").split(":v")[-1]
    relative = Path(*MODULE.split(".")).with_suffix(".lean")
    item = next(row for row in files if row["path"] == f"src/{relative.as_posix()}")
    receipt = {
        "pinned_commit": PIN, "mathlib_commit": math_pin, "lean_toolchain": lean_version,
        "module": MODULE, "declaration": THEOREM, "source_git_blob": item["git_blob"],
        "raw_sha256": item["sha256"], "complete_source_blobs_verified": len(files),
        "scope": "One original module rebuilt and checked; precompiled Mathlib dependencies.",
        "commands": []
    }
    with tempfile.TemporaryDirectory(prefix="siegel-cell-") as tmp:
        stage = Path(tmp)
        staged = stage / relative
        staged.parent.mkdir(parents=True)
        shutil.copyfile(source / "src" / relative, staged)
        probe = stage / "AxiomReport.lean"
        probe.write_text(f"import {MODULE}\n#print axioms {THEOREM}\n")
        import_dirs = [stage, mathlib / ".lake/build/lib/lean",
                       *sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean")),
                       sdk / "lib/lean"]
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, import_dirs)),
                   LEAN_SYSROOT=str(sdk), PATH=str(sdk / "bin") + os.pathsep + os.environ["PATH"])
        commands = [["lean", "--version"], ["lean", "-o", str(relative.with_suffix(".olean")),
                    str(relative)], ["lean", probe.name], ["leanchecker", MODULE]]
        for command in commands:
            start = time.monotonic()
            exe = command[0] + (".exe" if os.name == "nt" else "")
            completed = subprocess.run([str(sdk / "bin" / exe), *command[1:]],
                                       cwd=stage, env=env, text=True, capture_output=True)
            record = dict(arguments=command, exit_code=completed.returncode,
                          elapsed_s=round(time.monotonic()-start, 3),
                          stdout=completed.stdout, stderr=completed.stderr)
            receipt["commands"].append(record)
            if completed.returncode:
                return receipt, completed.returncode
            if command == commands[0] and f"version {lean_version}," not in completed.stdout:
                raise ValueError(f"Expected Lean {lean_version}; received {completed.stdout.strip()}")
    return receipt, 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, type=Path, help="Original tree containing src/")
    parser.add_argument("--repo", required=True, type=Path, help="Git checkout containing original commit")
    parser.add_argument("--sdk", required=True, type=Path, help="Lean SDK containing bin/lean and bin/leanchecker")
    parser.add_argument("--mathlib", required=True, type=Path, help="Pinned, built Mathlib checkout")
    parser.add_argument("--receipt", type=Path, help="Optional JSON output path; defaults to stdout")
    args = parser.parse_args()
    receipt, status = run(*(p.expanduser().resolve() for p in
                            (args.source, args.repo, args.sdk, args.mathlib)))
    body = json.dumps(receipt, indent=2) + "\n"
    if args.receipt:
        args.receipt.write_text(body)
    else:
        sys.stdout.write(body)
    return status


if __name__ == "__main__":
    sys.exit(main())
