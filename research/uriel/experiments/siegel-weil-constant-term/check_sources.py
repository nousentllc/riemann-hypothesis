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


def passage_digest(lines, spans):
    """Hash exactly the selected line ranges, including their identity and length."""
    checksum = sha256()
    for low, high in spans:
        if not 1 <= low <= high <= len(lines):
            raise ValueError(f"Invalid source range {low}–{high} in {len(lines)} lines")
        segment = b"".join(lines[low - 1:high])
        checksum.update(f"{low}:{high}:{len(segment)}\n".encode("ascii"))
        checksum.update(segment)
    return checksum.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, help="Git checkout containing the original commit")
    parser.add_argument("--source", type=Path, default=HERE / "original", help="directory containing src/")
    args = parser.parse_args()
    ledger = json.loads((HERE / "source_trace.json").read_text())
    commit = ledger["commit"]
    tree = original_tree(args.repo, commit) if args.repo else {}
    paths = set()
    spans = 0
    for row in ledger["files"]:
        path, blob = row["path"], row["git_blob"]
        if path in paths or not path.startswith("src/") or ".." in Path(path).parts:
            raise ValueError(f"Invalid or duplicate source path {path}")
        paths.add(path)
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
        intervals = row["spans"]
        if not intervals or intervals != sorted(intervals) or len({tuple(s) for s in intervals}) != len(intervals):
            raise ValueError(f"Missing, duplicated, or unsorted spans for {path}")
        if passage_digest(lines, intervals) != row["passages_sha256"]:
            raise ValueError(f"Changed source passages for {path}")
        spans += len(intervals)
    print(f"Verified {len(paths)} original files and {spans} source passages.")
    if args.repo:
        print(f"All files match the Git tree at {commit}.")


if __name__ == "__main__":
    main()
