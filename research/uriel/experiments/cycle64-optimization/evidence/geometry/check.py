"""Verify the two-direction count formula and reproduce the tree ceiling panel."""
import argparse
import json
import os
import subprocess
import tempfile
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def ceiling(x, d):
    return (x+d-1)//d


def formula(m, e, o):
    if not e or not o:
        return 0, 1
    candidates = [(m,m)]
    s = 1
    while s < m:
        k = ceiling(e,s)+ceiling(o,s)-1
        candidates.append((2*s*ceiling(k,2),s))
        s *= 2
    return min(candidates)


def literal(m, left, right):
    delta = {(v-u) % m for u in left for v in right}
    return len(delta | {(-1-h) % m for h in delta})


def make_sets(m, e, o):
    size,s = formula(m,e,o)
    if not e or not o or size==m:
        return list(range(e)),list(range(o))
    quotient = m//s
    a,b = ceiling(e,s),ceiling(o,s)
    length = a+b-1
    # D = [offset-a+1, offset+b-1]. Center its enclosing even-length
    # interval on -1/2. If odd, one additional endpoint suffices.
    offset = (a-1-ceiling(length,2)) % quotient
    def fill(count,start):
        return [((start+k) % quotient)+j*quotient for k in range(ceiling(count,s))
                for j in range(s)][:count]
    return fill(e,0),fill(o,offset)


def run():
    exhaustive = {}
    for m in (1,2,4,8):
        subsets = [[i for i in range(m) if mask>>i&1] for mask in range(1<<m)]
        minima = {}
        for a in subsets:
            for b in subsets:
                key = len(a),len(b)
                minima[key] = min(minima.get(key,m),literal(m,a,b))
        assert all(formula(m,*key)[0]==minimum for key,minimum in minima.items())
        exhaustive[m] = (1<<m)**2
    constructions = 0
    for m in (1,2,4,8,16,32):
        for e in range(m+1):
            for o in range(m+1):
                a,b = make_sets(m,e,o)
                assert len(set(a))==e and len(set(b))==o
                assert literal(m,a,b)==formula(m,e,o)[0]
                constructions += 1
    caps = [F(1),F(3,2),F(2),F(9,4),F(19,8),F(12,5),F(3),F(4),F(8),F(1631,100)]
    rows = []
    with tempfile.TemporaryDirectory() as td:
        exe = Path(td)/"ceiling"
        subprocess.run([os.environ.get("CXX","c++"),"-std=c++17","-O3",
                        str(ROOT/"ceiling.cpp"),"-o",str(exe)],check=True)
        def solve(width,cap,reflected):
            fields = list(map(int,subprocess.check_output([str(exe),str(width),
                str(cap.numerator),str(cap.denominator),str(int(reflected))],text=True).split()))
            w,c,b,rev,p,q,it,top,bottom = fields
            assert (w,F(c,b),rev)==(width,cap,reflected)
            assert q*top-p*bottom==0 and bottom>0 and 0<=p<q
            return {"optimum":str(F(p,q)), "iterations":it, "last_numerator":top,
                    "last_denominator":bottom}
        for cap in caps:
            one,two = solve(64,cap,False),solve(64,cap,True)
            assert F(one["optimum"])>=F(two["optimum"])
            rows.append({"cap":str(cap),"oriented_only":one,"both":two})
        assert F(rows[0]["both"]["optimum"])==0
        assert F(solve(2,F(12,5),True)["optimum"])==0
        assert F(solve(4,F(12,5),True)["optimum"])==0
    return {"exhaustive_ordered_set_pairs":exhaustive,"constructive_count_pairs":constructions,"rows":rows}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--check",action="store_true")
    args = p.parse_args()
    data = run()
    text = json.dumps(data,indent=2)+"\n"
    output = ROOT/"results.json"
    if args.check:
        assert output.read_text()==text
    else:
        output.write_text(text)
    for row in data["rows"]:
        print(row["cap"],row["both"]["optimum"],float(F(row["both"]["optimum"])))


if __name__=="__main__":
    main()
