"""Check every source passage against the frozen ledger and, optionally, the published Git tree."""
import argparse
from hashlib import sha1, sha256
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent


def original_tree(repo, commit):
    listing = subprocess.check_output(["git", "-C", repo, "ls-tree", "-r", "-z", commit, "--", "src"])
    entries = {}
    for item in listing.split(b"\0"):
        if item:
            info, path = item.split(b"\t", 1)
            entries[path.decode()] = info.split()[2].decode()
    return entries


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, help="Git checkout containing the original commit")
    parser.add_argument("--source", type=Path, default=HERE / "original", help="directory containing src/")
    args = parser.parse_args()
    ledger = json.loads((HERE / "source_trace.json").read_text())
    commit = ledger["commit"]
    tree = original_tree(args.repo, commit) if args.repo else {}
    spans = calls = 0
    for row in ledger["files"]:
        path, blob = row["path"], row["git_blob"]
        if args.repo and tree.get(path) != blob:
            raise ValueError(f"Unexpected source blob in the published Git tree: {path}")
        disk_path = args.source / path
        if disk_path.is_file():
            raw = disk_path.read_bytes()
        elif args.repo:
            raw = subprocess.check_output(["git", "-C", args.repo, "cat-file", "blob", blob])
        else:
            raise FileNotFoundError(f"{disk_path} is missing. Pass --repo or --source.")
        actual = sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        if actual != blob or sha256(raw).hexdigest() != row["sha256"]:
            raise ValueError(f"Source digest mismatch: {path}")
        lines = raw.splitlines(keepends=True)
        for span in row["spans"]:
            lo, hi = span["lines"]
            if not 1 <= lo <= hi <= len(lines):
                raise ValueError(f"Invalid source range: {path}, {lo}–{hi}")
            part = b"".join(lines[lo - 1:hi])
            if sha256(part).hexdigest() != span["sha256"]:
                raise ValueError(f"Changed source passage: {path}, {lo}–{hi}")
            for needle in span["body_anchors"]:
                if needle.encode() not in part:
                    raise ValueError(f"Missing proof-body reference: {path}: {needle}")
                calls += 1
            spans += 1
    print(f"Verified {len(ledger['files'])} original files, {spans} passages and {calls} proof-body references.")
    if args.repo:
        print(f"All files match the Git tree at {commit}.")


if __name__ == "__main__":
    main()
