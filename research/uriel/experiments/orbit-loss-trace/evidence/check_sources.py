"""Check source excerpts against the pinned Git tree and the reported line ranges."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path, help="Git repository containing the original commit")
    parser.add_argument("original", type=Path, help="extracted original source or complete checkout")
    args = parser.parse_args()
    entries = json.loads(Path(__file__).with_name("source_anchors.json").read_text())
    pin = "40e56bab026552e089d7afcfeff08d2defb9c005"
    if entries["commit"] != pin:
        raise ValueError("Unexpected source version")
    checked = 0
    for f in entries["files"]:
        path = f["path"]
        blob = subprocess.check_output(
            ["git", "-C", str(args.repo), "rev-parse", f"{pin}:{path}"], text=True).strip()
        contents = (args.original / path).read_bytes()
        framed = b"blob " + str(len(contents)).encode() + b"\0" + contents
        actual = hashlib.sha1(framed).hexdigest()
        if actual != blob or actual != f["git_blob"] or hashlib.sha256(contents).hexdigest() != f["sha256"]:
            raise ValueError(f"Source identity mismatch for {path}")
        lines = contents.decode().splitlines()
        for excerpt in f["ranges"]:
            if not 1 <= excerpt["start"] <= excerpt["end"] <= len(lines):
                raise ValueError(f"Invalid source range in {path}: {excerpt}")
            checked += 1
    print(f"Verified {len(entries['files'])} pinned files and {checked} source ranges.")


if __name__ == "__main__":
    main()
