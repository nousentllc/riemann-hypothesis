"""Enumerate modulo-sixteen supports and canonical child choices exactly."""
from fractions import Fraction
from itertools import combinations
from math import factorial
import json, argparse
from pathlib import Path


def exponential_upper(t):
    # t <= 16/7 < 3. Every later ratio after term 20 is <= 3/22.
    return sum(t**k / factorial(k) for k in range(21)) + t**21 / factorial(21) / (1-Fraction(3,22))


def solve():
    n=16
    rate=Fraction(16,7)
    assert exponential_upper(rate)<10
    safe = {(w, k, j): 10*rate*j/w > exponential_upper(rate*k/w)
            for w in (2,4,8,16) for k in range(w+1) for j in range(w//2+1)}
    for (width, count, even_count), passes in safe.items():
        if not passes:
            value = rate*count/width
            lower = sum(value**k/factorial(k) for k in range(21))
            assert 10*rate*even_count/width <= lower
    candidates=0; covered=set(); masks_used=[]; max_missing=0
    nodes=[(stride,c) for stride in (1,2,4,8) for c in range(stride)]
    for comb in combinations(range(n),7):
        mask=set(comb)
        en=sum(i%2==0 for i in mask)
        if min(en,7-en)<2:
            continue
        missing=[h for h in range(1,n,2) if all((t+h)%n not in mask for t in mask)]
        if not missing: continue
        candidates+=1
        choices=[0]
        for idx,(s,c) in enumerate(nodes):
            keys=(c,c+s)
            occ=[sum(t%(2*s)==j for t in mask) for j in keys]
            good=[b for b in (0,1) if not sum(occ) or safe[n//s,sum(occ),occ[b]]]
            choices=[v+(b<<idx) for v in choices for b in good]
            if not choices: break
        novel=len(set(choices)-covered)
        if novel:
            masks_used.append(dict(support=comb, absent=missing,new=novel))
            covered.update(choices)
            max_missing=max(len(missing),max_missing)
        if len(covered)==2**15:
            break
    left=[z for z in range(2**15) if z not in covered]
    return dict(orientations=2**15, covered=len(covered), uncovered=len(left),
                first_uncovered=left[:12], inspected_candidate_masks=candidates,
                covering_mask_count=len(masks_used),max_missing_among_cover=len(covered) and max_missing,
                certificates=masks_used)


def main():
    p=argparse.ArgumentParser(); p.add_argument("--check",action="store_true")
    args=p.parse_args()
    results=solve(); path=Path(__file__).with_name("stronger-results.json")
    content=json.dumps(results,indent=2)+"\n"
    if args.check: assert path.read_text()==content
    else: path.write_text(content)
    print({k:v for k,v in results.items() if k!="certificates"})


if __name__=="__main__":
    main()
