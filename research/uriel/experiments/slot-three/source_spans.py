"""Authenticate every linked original-source span in this experiment's Markdown."""
import argparse
from hashlib import sha256
from pathlib import Path
import re

from build_tower import HERE, PIN, dump, pinned_tree
from build_original import pinned_source

PREFIX = "https://github.com/nousentllc/riemann-hypothesis/blob/"
SOURCE = re.compile(re.escape(PREFIX) + r"([^/]+)/(?P<path>src/[^)\s#]+\.lean)#L(\d+)(?:-L(\d+))?\)")


def run(source, out):
    tree = pinned_tree()
    files, spans = {}, {}
    for doc in sorted(HERE.glob("*.md")):
        body = doc.read_text()
        for link in re.findall(re.escape(PREFIX) + r"[^)\s]+/src/[^)\s]+\)", body):
            m = SOURCE.fullmatch(link)
            if not m or m[1] != PIN:
                raise ValueError(f"Source link missing pinned anchor: {doc.name}: {link}")
            path, lo, hi = m[2], int(m[3]), int(m[4] or m[3])
            if path not in files:
                files[path] = pinned_source(Path(path), source, tree).splitlines(keepends=True)
            lines = files[path]
            if not 1 <= lo <= hi <= len(lines):
                raise ValueError(link)
            key=(path,lo,hi)
            if key not in spans:
                spans[key]={"path":path, "first":lo, "last":hi, "source_blob":tree[path],
                            "sha256":sha256(b"".join(lines[lo-1:hi])).hexdigest(), "cited_by":[]}
            if doc.name not in spans[key]["cited_by"]:
                spans[key]["cited_by"].append(doc.name)
    if not spans:
        raise ValueError("No pinned source spans found")
    dump(out,dict(pin=PIN,file_count=len(files),span_count=len(spans),spans=[spans[k] for k in sorted(spans)]))
    print(f"Authenticated {len(spans)} spans in {len(files)} original files.")


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source",type=Path,required=True)
    ap.add_argument("--out",type=Path,required=True)
    args=ap.parse_args()
    run(args.source,args.out)
