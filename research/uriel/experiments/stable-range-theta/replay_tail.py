"""Compile and kernel-replay one exact original Haar comparison lemma in a Mathlib harness."""
import argparse
from hashlib import sha1, sha256
import json
import os
from pathlib import Path
import subprocess

PIN = "40e56bab026552e089d7afcfeff08d2defb9c005"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
LEAN = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
SOURCE = ("src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/"
          "ThetaParseval/ThetaKernels/TPGTail.lean")
HEADER = """import Mathlib
noncomputable section
open scoped NNReal
open MeasureTheory Filter Topology
namespace UpperTheory.TP
"""
FOOTER = """
#print axioms abs_tail_pk
end UpperTheory.TP
end
"""

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("source","repo","mathlib","toolchain","out"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    src, repo, mathlib, toolchain, out = [getattr(args, key).resolve() for key in
                                          ("source","repo","mathlib","toolchain","out")]
    out.mkdir(parents=True, exist_ok=True)
    version = subprocess.check_output([toolchain/"bin/lean","--version"], text=True).strip()
    if LEAN not in version:
        raise ValueError("Unexpected Lean version")
    mrev = subprocess.check_output(["git","-C",mathlib,"rev-parse","HEAD"],text=True).strip()
    if mrev != MATHLIB:
        raise ValueError("Unexpected Mathlib revision")
    expected = subprocess.check_output(["git","-C",repo,"rev-parse",PIN+":"+SOURCE],text=True).strip()
    raw = (src/SOURCE).read_bytes()
    actual = sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
    if actual != expected:
        raise ValueError("Original source does not match its Git blob")
    fragment = b"".join(raw.splitlines(keepends=True)[16:64])
    if not fragment.startswith(b"private theorem abs_tail_pk ") or b"sorry" in fragment:
        raise ValueError("Unexpected proof fragment")
    name = "HaarTailTransport"
    (out/(name+".lean")).write_bytes(HEADER.encode()+fragment+FOOTER.encode())
    libs=[out,mathlib/".lake/build/lib/lean",*sorted((mathlib/".lake/packages").glob("*/.lake/build/lib/lean"))]
    env=dict(os.environ, LEAN_PATH=os.pathsep.join(map(str,libs)), LEAN_SYSROOT=str(toolchain))
    logs=[]
    for cmd in [[toolchain/"bin/lean","-o",name+".olean",name+".lean"],
                [toolchain/"bin/leanchecker","-v",name]]:
        result=subprocess.run(cmd,cwd=out,env=env,text=True,capture_output=True)
        msg=(result.stdout+result.stderr).strip()
        print(msg,flush=True)
        if result.returncode:raise SystemExit(result.returncode)
        logs.append(msg)
    receipt={"source":SOURCE,"original":PIN,"blob":actual,"lines":[17,64],
             "fragment_sha256":sha256(fragment).hexdigest(),"wrapper_sha256":sha256((out/(name+".lean")).read_bytes()).hexdigest(),
             "mathlib":mrev,"lean":version,"compile_and_replay_output":logs,
             "scope":"Exact original private proof and statement, different import environment. Full TPGTail module and automorphic application not replayed here."}
    (out/"haar_tail_receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")

if __name__=="__main__":
    main()
