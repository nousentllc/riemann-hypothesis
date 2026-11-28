"""Authenticate the cited Mathlib files and the previously checked two-declaration source."""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

HERE=Path(__file__).resolve().parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def audit(ml):
    pins=json.loads((HERE/"source_map.json").read_text())
    rev=subprocess.check_output(["git","-C",ml,"rev-parse","HEAD"],text=True).strip()
    assert rev==pins["mathlib_commit"]
    for record in pins["mathlib"]:
        path=record["path"]
        raw=(ml/path).read_bytes()
        assert digest(raw)==record["sha256"]
        obj=subprocess.check_output(["git","-C",ml,"rev-parse",rev+":"+path],text=True).strip()
        assert record["git_blob"]==obj==hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest()
        for line,text in record["anchors"]:
            assert text in raw.decode().splitlines()[line-1]
    text=(HERE/"SevenBase.lean").read_text()
    restored=text.split("/-- The starting condition")[0]+"#print axioms seven_pid\n#print axioms base_class_number\nend SlotSevenProbe\n"
    assert digest(restored.encode())==pins["prior_base_source_sha256"]
    return dict(mathlib_revision=rev,authenticated_mathlib_files=len(pins["mathlib"]),
                prior_base_source_restored=True,prior_base_sha256=digest(restored.encode()))


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--mathlib",type=Path,required=True)
    print(json.dumps(audit(ap.parse_args().mathlib.resolve()),indent=2))
