"""Verify the files and rerun the finite selected-place controls."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys


def main():
    if not __debug__:
        raise SystemExit("Run with ordinary Python assertions enabled.")
    root = Path(__file__).resolve().parent
    for line in (root / "SHA256SUMS").read_text().splitlines():
        expected, path = line.split("  ", 1)
        if sha256((root / path).read_bytes()).hexdigest() != expected:
            raise ValueError(f"File hash differs: {path}")
    calculated = subprocess.check_output([sys.executable, "-B", root / "controls.py"], cwd=root)
    if calculated != (root / "control_results.json").read_bytes():
        raise ValueError("Finite controls differ from the archived results.")
    receipt = json.loads((root / "replay_receipt.json").read_text())
    names = set()
    for run in receipt["runs"]:
        for record in run["experiment_modules"]:
            name = record["module"]
            names.add(name)
            if sha256((root / (name + ".lean")).read_bytes()).hexdigest() != record["source_sha256"]:
                raise ValueError(f"Replay source changed: {name}")
            if record["kernel"] != f"replaying {name}" or "sorry" in record["elaboration"]:
                raise ValueError(f"Unexpected archived replay result: {name}")
    if names != {"ReadableCapacity", "OriginalCapacity", "SameSet"}:
        raise ValueError("Missing proof module in replay inventory.")
    print("Checksums, proof inventory and finite controls match.")


if __name__ == "__main__":
    main()
