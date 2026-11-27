"""Replay legacy numerical controls in a temporary copy of their original layout."""

import argparse
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent


def python(directory, *arguments, capture=False):
    return subprocess.run(
        [sys.executable, "-B", *arguments], cwd=directory, check=True,
        stdout=subprocess.PIPE if capture else None,
    )


def compare(directory, expected, *arguments):
    actual = python(directory, *arguments, capture=True).stdout
    if actual != (directory / expected).read_bytes():
        raise SystemExit(f"Saved results differ in {directory.name}/{expected}")
    print(f"Reproduced {directory.name}/{expected}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True, help="Local Riemann Git repository with the pinned study history")
    repo = parser.parse_args().repo.resolve(strict=True)
    with tempfile.TemporaryDirectory(prefix="riemann-archive-replay-") as path:
        work = Path(path)
        (work / "riemann-experiments").symlink_to(repo, target_is_directory=True)
        output = work / "output"
        for name in ("research-assessment", "slot3-witness-memory", "changing-cutoff-reader", "companion-independent-counts"):
            shutil.copytree(HERE / name, output / name)
        slot = output / "slot3-witness-memory"
        reader = output / "changing-cutoff-reader"
        companion = output / "companion-independent-counts"
        python(slot, "-m", "unittest", "test_benchmark.py")
        python(reader, "-m", "unittest", "test_reader.py")
        compare(slot, "results.json", "benchmark.py", "--repo", str(repo))
        compare(slot / "allocation", "results.json", "allocation.py", "--repo", str(repo))
        compare(reader, "results.json", "run.py")
        prior = (companion / "independent_counts.json").read_bytes()
        python(companion, "independent_counts.py", capture=True)
        if (companion / "independent_counts.json").read_bytes() != prior:
            raise SystemExit("Independent companion census differs from the saved output")
        print("Reproduced companion-independent-counts/independent_counts.json")


if __name__ == "__main__":
    main()
