"""Authenticate the original statements and proof bodies in the semilinear transport subset."""
from hashlib import sha256
from pathlib import Path
import argparse
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"joint-witness"))
from build_original import PIN, pinned_source, pinned_tree

MODULE="src/Development/AutomorphicSpectrum/Proofs/GlobalProofs/CohomologicalDimensionTopologicalIso.lean"
SPANS=((11,156),(187,225))
HEADER="""/- Selected transport declarations from the pinned CohomologicalDimensionTopologicalIso module.
The source intervals and local wrapper are authenticated by check_excerpt.py. -/
import GroundTheory.GlobalFields.ClassFieldConsequences.HilbertClassField
open NumberField IsDedekindDomain GroundTheory.ProfCoh
namespace Ascent.Semi
"""
FOOTER="end NumberFields\nend Ascent.Semi\n"


def verify(source):
    tree=pinned_tree()
    lines=pinned_source(Path(MODULE),source,tree).splitlines(keepends=True)
    portions=[b"".join(lines[a-1:b]) for a,b in SPANS]
    full=HEADER.encode()+b"".join(portions)+FOOTER.encode()
    if full!=(HERE/"SemilinearTransport.lean").read_bytes():
        raise ValueError("The selected declarations or their wrapper changed")
    return {"commit":PIN,"file":MODULE,"blob":tree[MODULE],"spans":[
      {"start":a,"end":b,"sha256":sha256(part).hexdigest()} for (a,b),part in zip(SPANS,portions)],
      "wrapped_sha256":sha256(full).hexdigest()}


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source",required=True,type=Path)
    print(json.dumps(verify(p.parse_args().source),sort_keys=True,indent=2))
