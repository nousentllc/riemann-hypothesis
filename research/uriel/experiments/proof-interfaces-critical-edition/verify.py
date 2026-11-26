"""Verify archived file integrity and reproduce the independent finite comparisons."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, help="Optional Git checkout containing the historical PDF revisions")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    if not __debug__:
        raise SystemExit("Use ordinary Python so assertions in the finite experiments run.")
    for line in (root / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError(f"Digest mismatch: {name}")
    tests = [
        ("controls.py", "control_results.json"),
        ("evidence/architecture/controls.py", "evidence/architecture/controls.json"),
        ("evidence/interface/finite_controls.py", "evidence/interface/finite_results.json"),
        ("evidence/density/finite_checks.py", "evidence/density/finite_results.json"),
        ("evidence/density/digit_certificate.py", "evidence/density/digit_certificate.json"),
        ("evidence/density/valuation_census.py", "evidence/density/valuation_counts.json"),
    ]
    for script, record in tests:
        actual = json.loads(subprocess.check_output([sys.executable, "-B", root / script], cwd=root))
        if actual != json.loads((root / record).read_text()):
            raise ValueError(f"Finite comparison differs: {script}")
        print("Matched", record)
    inventory = json.loads((root / "inventory.json").read_text())
    assert len(inventory) == 16
    if args.repo:
        for row in inventory:
            spec = row["commit"] + ":" + row["source"]
            blob = subprocess.check_output(["git", "-C", args.repo.resolve(), "show", spec])
            if hashlib.sha256(blob).hexdigest() != row["sha256"]:
                raise ValueError(f"Historical PDF differs: {spec}")
        print("Matched all 16 audited PDFs to their historical Git revisions.")
    assert len(list(root.rglob("*.tex"))) == 1 and len(list(root.rglob("*.pdf"))) == 1


if __name__ == "__main__":
    main()
