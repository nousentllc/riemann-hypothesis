"""Bracket the marked optimum on the displayed adverse word, via every support."""
import argparse
import json
import os
import subprocess
import sys
import tempfile
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "rates"))
from verify import tile_interval, CL, BETA, HALF

def ledger(word, support):
    rows = [[1, 0] for _ in range(64)]  # Q, P
    forms = []
    for stride in (1, 2, 4, 8, 16, 32):
        width = 64 // stride
        for residue in range(stride):
            node = [t for t in support if t % stride == residue]
            if not node:
                continue
            even = residue + stride * ((word >> (stride-1+residue)) & 1)
            ev = [t for t in node if t % (2*stride) == even]
            assert ev
            d = sum(all((t+h*stride) % 64 not in node for t in node)
                    for h in range(1,width,2))
            for t in set(node)-set(ev):
                rows[t][0] += width
                rows[t][1] += 2*d
            forms.append((width,node,ev))
    return rows,forms

def run(exe):
    frozen = json.loads((HERE.parent/"upper/results.json").read_text())
    word = int(frozen["label_word"])
    support = frozen["vertex"]["support"]
    tail = frozen["vertex"]["partial_rate_leaf"]
    rows,forms = ledger(word, support)
    def profile(c):
        return {t:(64-26*c if t==tail else c) for t in support}
    def value(c):
        rates=profile(c)
        return (sum(rows[t][1]*a for t,a in rates.items()) /
                sum(rows[t][0]*a for t,a in rates.items()))
    a=profile(CL)
    margins=[tile_interval(sum(a[t] for t in group)/w,sum(a[t] for t in even)/w)[0]
             for w,group,even in forms]
    margins += [tile_interval(x,x/2)[0] for x in a.values()]
    assert min(margins)>0
    checks=[]
    for cap,exponent in [(F(239209,100000),BETA),(F(23921,10000),HALF)]:
        # For a positive homogeneous leaf with a>2, the test decreases at larger a.
        assert tile_interval(cap,cap/2,exponent)[1]<0
        z=value(cap)
        assert z.numerator<2**31 and z.denominator*127*64*cap.denominator<2**60
        cmd=[str(exe),str(word),str(z.denominator),str(cap.numerator),str(cap.denominator)]
        line=" ".join([str(z.numerator)]+["0"]*64)+"\n"
        value_out,caps,partial=map(int,subprocess.check_output(cmd,input=line,text=True).split())
        assert value_out==0 and caps.bit_count()==26 and partial.bit_count()==1
        checks.append({"cap":str(cap),"upper":str(z),"maximum_residual":value_out})
    return {"label_word":str(word),"witness_lower":str(value(CL)),
            "full_rate":str(CL),"residual_rate":str(a[tail]),"partial_leaf":tail,
            "occupied_cells_and_leaf_checks":len(margins),
            "minimum_log_mark_margin_exceeds":"1/100000000000" if min(margins)>F(1,10**11) else "0",
            "closed_box_checks":checks}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--write",action="store_true")
    args=parser.parse_args()
    with tempfile.TemporaryDirectory() as td:
        exe=Path(td)/"fixed"
        subprocess.run([os.environ.get("CXX","c++"),"-std=c++17","-O3",
                        str(HERE/"priced.cpp"),"-o",str(exe)],check=True)
        obj=run(exe)
    out=HERE/"fixed_label.json"
    if args.write:
        out.write_text(json.dumps(obj,indent=2)+"\n")
    else:
        assert json.loads(out.read_text())==obj
    print(json.dumps(obj))

if __name__=="__main__":
    main()
