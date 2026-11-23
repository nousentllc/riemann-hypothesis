"""Evaluate the affine six-hole construction over two deterministic labeling panels."""
from argparse import ArgumentParser
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
from random import Random
import json

Q = 64
ALL = (1 << Q) - 1
RATE = F(64, 27)
NODES = [(s, c, sum(1 << t for t in range(c, Q, 2*s)),
          sum(1 << t for t in range(c+s, Q, 2*s)))
         for s in (1, 2, 4, 8, 16, 32) for c in range(s)]


def rotate(mask, step):
    return ((mask << step) & ALL) | (mask >> (Q-step))


@lru_cache(None)
def tile(k, e, w):
    if not k:
        return True
    if not e:
        return False
    mu, nu = RATE * k / w, RATE * e / w
    term = lo = F(1)
    for i in range(1, 29):
        term *= mu/i
        lo += term
    hi = lo + term * mu / 29 / (1-mu/30)
    exponent, target = (2,100*nu) if nu <= 1 else (13,10**13 * nu**6)
    assert not (lo**exponent < target <= hi**exponent)
    return hi**exponent < target


def templates():
    catalog = {}
    for t in range(1, 27):
        even = set(range(0, 2*t, 2))
        holes = {(y+h) % Q for y in even for h in (-5,-3,-1,1,3,5)}
        original = even | (set(range(1,Q,2)) - holes)
        assert len(original) == 27
        for u in range(1, Q, 2):
            transformed = sum(1 << (u*y % Q) for y in original)
            for z in range(Q):
                mask = rotate(transformed, z)
                catalog.setdefault(mask, (t,u,z))
    return catalog


def coefficients(mask):
    zeros, ones, qzeros, qones = 0, 0, 0, 0
    features = []
    for i,(s,c,first,second) in enumerate(NODES):
        w = Q//s
        a, b = (mask & first).bit_count(), (mask & second).bit_count()
        if not a+b:
            continue
        if not a:
            ones |= 1 << i
        if not b:
            zeros |= 1 << i
        if not tile(a+b,a,w):
            qones |= 1 << i
        if not tile(a+b,b,w):
            qzeros |= 1 << i
        node = mask & (first | second)
        missing = sum(not(node & rotate(node,h)) for h in range(s,Q,2*s))
        features.append((i,w,missing,a,b))
    return zeros,ones,qzeros,qones,features


def run():
    candidates=templates()
    rng=Random(19031)
    words=[0]+[rng.getrandbits(63) for _ in range(128)]
    az=[0]*len(words)
    counts=[0]*len(words)
    best=[(F(0),None)]*len(words)
    assert tile(2,1,2)
    for mask,shape in candidates.items():
        zeros,ones,qzeros,qones,features=coefficients(mask)
        for i,word in enumerate(words):
            if word & zeros or (word & ones) != ones:
                continue
            az[i]+=1
            if word & qzeros or (word & qones) != qones:
                continue
            counts[i]+=1
            num,den=0,27
            for bit,w,missing,a,b in features:
                odd = a if word >> bit & 1 else b
                num += 2 * missing * odd
                den += w * odd
            score=F(num,den)
            if score>best[i][0]:
                best[i]=score,shape
    example = next((i for i in range(len(words)) if az[i]==0),None)
    def describe(i):
        return dict(orientation=str(words[i]),geometric_candidates=az[i],
                    mark_candidates=counts[i],best_ratio=str(best[i][0]),best_template=best[i][1])
    return dict(distinct_templates=len(candidates),affine_parameter_triples=26*32*64,
                test_orientations=len(words),orientation_zero=describe(0),
                orientations_passing_ten_percent=sum(v[0]>=F(1,10) for v in best),
                no_even_child_candidate=sum(x==0 for x in az),
                no_mark_candidate=sum(x==0 for x in counts),
                first_even_child_obstruction=describe(example) if example is not None else None)


def main():
    ap=ArgumentParser(description=__doc__)
    ap.add_argument("--check",action="store_true")
    args=ap.parse_args()
    path=Path(__file__).with_name("results.json")
    output=json.dumps(run(),indent=2)+"\n"
    if args.check:
        assert output==path.read_text()
    else:
        path.write_text(output)
    print(output,end="")


if __name__=="__main__":
    main()
