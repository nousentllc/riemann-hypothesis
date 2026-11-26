"""Check the literal original-host extension in the pinned native environment."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

from replay import ROOT, TOOLCHAINS, checked_run, resolve_checkout


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for key in ("sdk", "original", "old-mathlib", "old-objects"):
        p.add_argument("--" + key, type=Path, required=True)
    args = p.parse_args()
    args.mode = "original"
    trace = json.loads((ROOT / "source_trace.json").read_text())
    _, mathlib, libraries = resolve_checkout(args, trace)
    sdk = args.sdk.resolve()
    version = subprocess.check_output([sdk / "bin/lean", "--version"], text=True).strip()
    revision = subprocess.check_output(["git", "-C", mathlib, "rev-parse", "HEAD"], text=True).strip()
    expected_sdk, expected_mathlib = TOOLCHAINS["original"]
    if expected_sdk not in version or revision != expected_mathlib:
        raise ValueError("Unexpected native compiler or Mathlib.")
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        original = checked_run(ROOT / "OriginalCapacity.lean", work, sdk, libraries)
        extension = checked_run(ROOT / "SingleCoset.lean", work, sdk, libraries)
    print(json.dumps(dict(compiler=version, mathlib=revision, original=original, extension=extension), indent=2))


if __name__ == "__main__":
    main()
