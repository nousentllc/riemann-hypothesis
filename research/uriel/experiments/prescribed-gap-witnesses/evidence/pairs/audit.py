"""Recheck source blobs and exact declaration spans used in the pair-sharing experiment."""
from pathlib import Path
from hashlib import sha1,sha256
import argparse
import json
import subprocess

PIN="40e56bab026552e089d7afcfeff08d2defb9c005"
HERE=Path(__file__).resolve().parent
AA="src/Development/AutomorphicArithmetic/"
CB=AA+"CharacterBoxes/"
MS=AA+"MeanSquareBounds/"
CM=AA+"AutomorphicVarieties/CMFieldExponentialBounds/"
SPANS={CB+"ExistsPageN.lean":[(19,25),(27,37),(39,49)],
       CB+"PairGood.lean":[(9,16),(18,30),(41,42)],
       CB+"WinPairs.lean":[(9,16),(26,35),(52,68)],
       MS+"PrimeSetTwoBounds.lean":[(35,53),(55,65)],
       MS+"PairShare.lean":[(27,36)], MS+"PairExists.lean":[(9,17),(27,43)],
       MS+"pairEx.lean":[(11,23),(112,130),(139,151),(152,169)],
       CM+"AdmissibleOfPageN.lean":[(41,60),(61,88)],
       "src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean":[(26,30),(40,43)]}

def audit(source,gitroot=None):
    records=[]
    for name,spans in sorted(SPANS.items()):
        raw=(source/name).read_bytes()
        blob=sha1(b"blob "+str(len(raw)).encode()+b"\x00"+raw).hexdigest()
        if gitroot:
            sha=subprocess.check_output(["git","-C",str(gitroot),"rev-parse",PIN+":"+name],text=True).strip()
            if sha!=blob:raise ValueError(name)
        lines=raw.splitlines(keepends=True)
        assert all(1<=lo<=hi<=len(lines) for lo,hi in spans)
        records.append(dict(path=name,blob=blob,sha256=sha256(raw).hexdigest(),spans=[
            dict(start=lo,end=hi,sha256=sha256(b"".join(lines[lo-1:hi])).hexdigest()) for lo,hi in spans]))
    return dict(pin=PIN,files=records)

if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--source",type=Path,required=True)
    cli.add_argument("--git",type=Path)
    cli.add_argument("--register",action="store_true")
    a=cli.parse_args()
    out=audit(a.source,a.git)
    if a.register:
        if not a.git:cli.error("register requires --git")
        print(json.dumps(out,indent=2))
    else:
        if out!=json.loads((HERE/"source_map.json").read_bytes()):
            raise ValueError("original source trace differs")
        print(json.dumps(dict(pin=PIN,files=len(out["files"]),spans=sum(len(r["spans"]) for r in out["files"])),indent=2))
