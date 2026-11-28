"""Authenticate cited original Lean sources and check every linked line range."""
import argparse
from collections import defaultdict
from hashlib import sha1, sha256
import json
from pathlib import Path
import re
import subprocess
from urllib.parse import unquote


PIN = "40e56bab026552e089d7afcfeff08d2defb9c005"
REQUIRED = {
    "Development/AutomorphicArithmetic/ThickFrames/select.lean": (136, "obtain ⟨T, hT0, hT⟩ := sel_exists"),
    "Development/AutomorphicArithmetic/ThickFrames/topsGroup.lean": (95, "UpperTheory.BernoulliSumsFrobeniusOrbits.select"),
    "Formalism/SubspaceCounting/GoodOrbitIntervalTileCondition.lean": (13, "def Marked"),
    "Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean": (239, "def goodU"),
}
ROOT = Path(__file__).resolve().parents[1]
URL = re.compile(r"github\.com/nousentllc/riemann-hypothesis/blob/" + PIN +
                 r"/src/([^#)\s]+\.lean)#L(\d+)(?:-L(\d+))?")
ORIG = re.compile(r"\\orig\{([^{}]+)\}\{(\d+)\}\{")


def citations():
    found = defaultdict(set)
    for doc in sorted(ROOT.rglob("*")):
        if doc.suffix not in (".tex", ".md"):
            continue
        text = doc.read_text()
        loc = doc.relative_to(ROOT).as_posix()
        for path, begin, end in URL.findall(text):
            found[unquote(path)].add((loc, int(begin), int(end or begin)))
        for path, line in ORIG.findall(text):
            found[path + ".lean"].add((loc, int(line), int(line)))
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--original", type=Path, required=True,
                        help="extracted original tree containing src/")
    parser.add_argument("--write", action="store_true", help="regenerate the saved manifest")
    args = parser.parse_args()
    tree = subprocess.check_output(["git", "-C", args.repo, "ls-tree", "-rz", PIN, "src"])
    objects = {}
    for record in tree.split(b"\0"):
        if record:
            meta, path = record.split(b"\t", 1)
            objects[path.decode()] = meta.split()[2].decode()
    entries = []
    references = citations()
    missing = set(REQUIRED) - set(references)
    if missing:
        raise ValueError(f"Required pinned modules lack citations: {sorted(missing)}")
    for path, spans in sorted(references.items()):
        key = "src/" + path
        data = (args.original / key).read_bytes()
        blob = sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if blob != objects[key]:
            raise ValueError("Original source differs from pinned blob: " + key)
        lines = len(data.splitlines())
        if path in REQUIRED:
            line, landmark = REQUIRED[path]
            if not any(start <= line <= end for _, start, end in spans):
                raise ValueError(f"Missing reference to {key} line {line}")
            if landmark and landmark not in data.decode().splitlines()[line-1]:
                raise ValueError(f"Missing textual landmark in {key} line {line}")
        if any(not (1 <= a <= b <= lines) for _, a, b in spans):
            raise ValueError("Out of range: " + key)
        entries.append({"source":key, "git_blob":blob, "sha256":sha256(data).hexdigest(),
                        "lines":lines, "cited_at":sorted(spans)})
    result = json.dumps({"pin":PIN,"sources":entries}, ensure_ascii=False, indent=2) + "\n"
    target = Path(__file__).with_name("source_anchors.json")
    if args.write:
        target.write_text(result)
    elif result != target.read_text():
        raise ValueError("Saved citation manifest differs")
    print(f"Authenticated {len(entries)} files and {sum(len(s['cited_at']) for s in entries)} citation ranges.")


if __name__ == "__main__":
    main()
