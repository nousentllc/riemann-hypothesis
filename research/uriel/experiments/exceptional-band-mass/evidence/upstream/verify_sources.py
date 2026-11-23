"""Check pinned Git-blob, full text, and individual line-range digests against a local source tree."""
import argparse
import hashlib
import json
from pathlib import Path


def verify(path):
    manifest=json.loads(Path(__file__).with_name("sources.json").read_bytes())
    spans=0
    for entry in manifest["entries"]:
        data=(path/entry["path"]).read_bytes()
        git_blob=hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()
        if git_blob!=entry["git_blob"] or hashlib.sha256(data).hexdigest()!=entry["sha256"]:
            raise ValueError(entry["path"])
        lines=data.splitlines(keepends=True)
        for span in entry["ranges"]:
            start,end=span["lines"]
            if not 1<=start<=end<=len(lines) or hashlib.sha256(b"".join(lines[start-1:end])).hexdigest()!=span["sha256"]:
                raise ValueError((entry["path"],start,end))
            spans+=1
    return {"source_commit":manifest["commit"],"files":len(manifest["entries"]),"line_ranges":spans}


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source",type=Path)
    print(json.dumps(verify(parser.parse_args().source),indent=2))
