"""Authenticate geometry source files and inclusive line spans in a pinned tree."""
import argparse
import hashlib
import json
from pathlib import Path

def validate(root):
    manifest = json.loads((Path(__file__).with_name("source_anchors.json")).read_text())
    spans = 0
    for item in manifest["files"]:
        data = (root/item["path"]).read_bytes()
        blob = hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()
        if blob != item["git_blob"] or hashlib.sha256(data).hexdigest() != item["sha256"]:
            raise ValueError("Source differs: "+item["path"])
        lines = data.splitlines(keepends=True)
        for anchor in item["anchors"]:
            lo, hi = anchor["lines"]
            if not 1 <= lo <= hi <= len(lines):
                raise ValueError("Invalid span: "+item["path"])
            if hashlib.sha256(b"".join(lines[lo-1:hi])).hexdigest() != anchor["sha256"]:
                raise ValueError("Source span differs: "+item["path"])
            spans += 1
    return {"pin":manifest["original_commit"], "files":len(manifest["files"]), "spans":spans}

if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source",type=Path,required=True)
    print(json.dumps(validate(parser.parse_args().source),indent=2))
