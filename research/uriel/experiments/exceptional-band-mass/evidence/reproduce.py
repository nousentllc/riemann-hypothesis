"""Reproduce finite results; optionally authenticate original files and run Lean."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
CHECKS = (
    ("upstream/checks.py", "upstream/control.json"),
    ("geometry/geometry_probe.py", "geometry/results.json"),
    ("geometry/subwindow_probe.py", "geometry/gap_receipt.json"),
    ("primes/bands.py", "primes/results.json"),
    ("primes/extrema_control.py", "primes/extrema_control.json"),
    ("primes/crossover.py", "primes/crossover.json"),
    ("bridge/chord.py", "bridge/results.json"),
)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def replay(script, receipt, args=(), platform_keys=()):
    cmd = [sys.executable, "-B", str(ROOT/script), *map(str, args)]
    result = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError(f"{script} failed:\n{result.stdout}\n{result.stderr}")
    actual = json.loads(result.stdout)
    expected = json.loads((ROOT/receipt).read_bytes())
    # Lean's banner contains the build platform; the replay programs independently
    # enforce the toolchain version and verify the Mathlib pin and axiom output.
    for key in platform_keys:
        actual.pop(key)
        expected.pop(key)
    if actual != expected:
        raise ValueError(f"{script} differs from {receipt}")
    print(f"PASS {script}", flush=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ("source","toolchain","mathlib"):
        parser.add_argument("--"+name,type=Path)
    args=parser.parse_args()
    if bool(args.toolchain)!=bool(args.mathlib):
        parser.error("Supply --toolchain and --mathlib together for both formal replays.")
    for line in (ROOT/"SHA256SUMS").read_text().splitlines():
        expected, path=line.split("  ",1)
        if sha((ROOT/path).read_bytes())!=expected:
            raise ValueError("Evidence checksum mismatch: "+path)
    print("PASS evidence checksums",flush=True)
    for script,receipt in CHECKS:
        replay(script,receipt)
    if args.source:
        src=args.source.resolve()
        replay("upstream/verify_sources.py","upstream/source_receipt.json",[src])
        replay("geometry/verify_anchors.py","geometry/source_verification.json",["--source",src])
    if args.toolchain:
        extra=["--toolchain",args.toolchain.resolve(),"--mathlib",args.mathlib.resolve()]
        replay("upstream/replay.py","upstream/kernel.json",extra,("lean",))
        replay("geometry/replay_geometry.py","geometry/kernel_receipt.json",extra,("lean",))


if __name__ == "__main__":
    main()
