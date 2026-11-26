"""Check archive files, rerun both finite studies and validate proof receipts."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    root = Path(__file__).resolve().parent
    for line in (root / "SHA256SUMS").read_text().splitlines():
        expected, filename = line.split("  ", 1)
        if digest(root / filename) != expected:
            raise ValueError(f"File hash differs: {filename}")
    for source, results in (("controls.py", "control_results.json"), ("expanded_checks.py", "expanded_results.json")):
        computed = subprocess.check_output([sys.executable, "-B", root / source], cwd=root)
        if computed != (root / results).read_bytes():
            raise ValueError(f"Finite results differ: {results}")
    previous = json.loads((root / "replay_receipt.json").read_text())
    extension = json.loads((root / "single_coset_receipt.json").read_text())
    for entry in [*(m for r in previous["runs"] for m in r["experiment_modules"]), extension]:
        module = entry["module"]
        if entry["source_sha256"] != digest(root / (module + ".lean")):
            raise ValueError(f"Archived source hash differs: {module}")
        if entry["kernel"] != "replaying " + module or "sorry" in entry["elaboration"]:
            raise ValueError(f"Archived replay did not pass: {module}")
    pdf, = list(root.glob("*.pdf"))
    _, = list(root.glob("*.tex"))
    publication = json.loads((root / "publication_check.json").read_text())
    if publication["pdf_sha256"] != digest(pdf) or publication["numbered_body_pages"] < 30:
        raise ValueError("The 30-page body report does not attest to the packaged PDF.")
    print("Checksums, both finite studies, proof receipts, and the 30-page publication check match.")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Use regular Python with assertions enabled.")
    main()
