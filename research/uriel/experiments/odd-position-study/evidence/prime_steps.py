"""Project concrete inert primes to the real cyclotomic group modulo 256."""
import argparse
from fractions import Fraction
import json
from math import fsum, isqrt, log
from pathlib import Path

from dyadic import direct_masks, tree_scores


def primes_before(cap):
    flags = bytearray(b"\x01") * cap
    flags[:2] = b"\x00\x00"
    for p in range(2,isqrt(cap-1)+1):
        if flags[p]:
            flags[p*p::p] = bytes((cap-1-p*p)//p+1)
    return [p for p in range(2,cap) if flags[p]]


def run():
    n, modulus, q, d = 64,256,163,25799
    logs = {}
    for h in range(n):
        residue = pow(5,h,modulus)
        for sign in (-1,1):
            u = (sign*residue) % modulus
            assert u not in logs
            logs[u] = h
    assert len(logs) == modulus//2
    qs = {i*i % q for i in range(1,q)}
    ds = {i*i % d for i in range(1,d)}
    hits = [(p,logs[p % modulus]) for p in primes_before(1000000)
            if p not in (2,q,d) and p % q not in qs and p % d not in ds]
    scores, _ = tree_scores(list(range(n)))
    masks = direct_masks(list(range(n)))
    sets = {"all_even":set(range(0,n,2)),"all_odd":set(range(1,n,2)),
            "highest_eighth":set(sorted(range(n),key=scores.__getitem__)[-8:]),
            "balanced_sparse":{0,7,14,21,34,41,48,55}}
    rows = []
    for H in (10000,100000,1000000):
        by_h = [[] for _ in range(n)]
        for p,h in hits:
            if p < H:
                by_h[h].append(log(p))
        mass = [fsum(v) for v in by_h]
        total = fsum(mass)
        row = {"cutoff":H,"count":sum(map(len,by_h)),"theta_over_cutoff":round(total/H,10),
               "generator_mass_fraction":round(fsum(mass[1::2])/total,10),"sets":{}}
        for name,T in sets.items():
            odd, unmatched, adjacent = [],[],[]
            for h in range(n):
                targets = T & masks[h]
                odd.append(len(targets))
                unmatched.append(sum((t-h)%n not in T for t in targets))
                adjacent.append(sum((t-h)%n in T for t in T))
            assert sum(adjacent)==len(T)**2 and sum(odd)==sum(scores[t] for t in T)
            assert all(0<=o-u<=a for o,u,a in zip(odd,unmatched,adjacent))
            def weighted(values):
                return round(fsum(w*v for w,v in zip(mass,values))/(total*len(T)),10)
            row["sets"][name]={"odd":weighted(odd),"unpaired":weighted(unmatched),
                               "uniform_odd":str(Fraction(sum(odd),n*len(T))),
                               "uniform_unpaired":str(Fraction(sum(unmatched),n*len(T)))}
        rows.append(row)
    return {"modulus":modulus,"q":q,"d":d,"rows":rows}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",type=Path)
    args=parser.parse_args()
    result=run()
    if args.check:
        assert json.loads(args.check.read_text())==result
        print("Reproduced the concrete prime-step table.")
    else:
        print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()
