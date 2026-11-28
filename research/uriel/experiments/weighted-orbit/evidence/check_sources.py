"""Check cited files against the original Git tree and a source archive."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

PIN = "40e56bab026552e089d7afcfeff08d2defb9c005"
HERE = Path(__file__).resolve().parent


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--checkout", type=Path, required=True)
    p.add_argument("--original", type=Path, required=True)
    args = p.parse_args()
    tex = (HERE.parent/"One_Exchange_and_the_Weighted_Orbit_Test.tex").read_text()
    anchors = {(path+".lean", int(line))
               for path,line in re.findall(r"\\orig\{([^}]+)\}\{(\d+)\}",tex)}
    for path,line in re.findall(r"/src/([^ )#]+\.lean)(?:#L(\d+))?",(HERE/"HOST.md").read_text()):
        anchors.add((path,int(line or 1)))
    paths = {}
    for name,line in sorted(anchors):
        data = (args.original/"src"/name).read_bytes()
        digest = hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()
        expected = subprocess.check_output(["git","-C",str(args.checkout),"rev-parse",PIN+":src/"+name],text=True).strip()
        assert digest == expected and 0 < line <= len(data.splitlines())
        row = paths.setdefault(name,{"git_blob":digest,"sha256":hashlib.sha256(data).hexdigest(),"lines":[]})
        row["lines"].append(line)
    print(json.dumps({"original_commit":PIN,"paths_relative_to_src":paths}, indent=2))


if __name__ == "__main__":
    main()
