"""Exact verification of the hand certificate for the weighted 64-leaf case."""
from argparse import ArgumentParser
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import json


@lru_cache(None)
def paired_tile(mu, nu):
    if mu == 0:
        return True
    term = lo = F(1)
    for j in range(1, 25):
        term *= mu/j
        lo += term
    hi = lo + term * mu/25/(1-mu/26)
    k, threshold = (2,100*nu) if nu <= 1 else (13,10**13*nu**6)
    assert not lo**k < threshold <= hi**k
    return hi**k < threshold


def uniform_tile_gates(rate, width, n):
    return [a for a in range(max(1,n-width//2),min(n,width//2)+1)
            if not paired_tile(rate*n/width,rate*a/width)]


def automorphisms(width):
    if width == 1:
        return [(0,)]
    h = width//2
    return [order for left in automorphisms(h) for right in automorphisms(h)
            for order in (left+tuple(i+h for i in right),tuple(i+h for i in left)+right)]


def canonically_possible(selected, width):
    return all(not any(z <= i < z+s for i in selected) or any(z <= i < z+s//2 for i in selected)
               for s in (2,4,8,16) if s<=width for z in range(0,width,s))


def dense_six():
    rows=[]
    for p in automorphisms(4):
        if p[3]>=2:
            removed = {3,6,7}
        elif p[3]==1:
            removed = {3,5,7}
        else:
            assert p[1]>=2
            removed = {1,6,7}
        kept=set(range(8))-removed
        assert canonically_possible(kept,8)
        assert any(i in removed and 4+p[i] in removed for i in range(4))
        exposure=sum(1+2*j for j in kept)
        rows.append(dict(pairing=list(p),removed=sorted(removed),internal_cost=exposure))
    assert max(row["internal_cost"] for row in rows)==33
    return rows


def bit_reverse_3(i):
    return (i//4) + (i&2) + 4*(i&1)


def layout(g):
    even = [2*bit_reverse_3(i) for i in g]
    return even + [(-1-i)%16 for i in reversed(even)]


def node_ledger(coords,ranks):
    w=len(coords)
    if not ranks:
        return []
    sites=set(coords[i] for i in ranks)
    if w==1:
        return [dict(w=1,sites=sorted(sites),score=-1)]
    h=w//2
    d=[s for s in range(1,w,2) if all((i+s)%w not in sites for i in sites)]
    odd=sum(i>=h for i in ranks)
    rows=[dict(w=w,sites=sorted(sites),missing=d,odd=odd,score=odd*(20*len(d)-w))]
    for j in range(2):
        rows += node_ledger([i//2 for i in coords[j*h:(j+1)*h]],
                            [i%h for i in ranks if i//h==j])
    return rows


def run():
    common=F(64,27)
    gate={}
    for w in (2,4,8,16,32,64):
        rng=range(1,min(27,w)+1) if w<64 else (27,)
        gate[w]=[(n,e) for n in rng for e in uniform_tile_gates(common,w,n)]
    assert not any(gate[w] for w in (2,4,8,16))
    assert gate[32]==[(n,1) for n in (14,15,16,17)] and gate[64]==[(27,1)]
    reservoir,odd_even,odd_odd=F(411,176),F(3,4),F(19,8)
    assert 22*reservoir+odd_even+5*odd_odd==64
    for rate in (reservoir,odd_odd):
        assert all(not uniform_tile_gates(rate,w,n) for w in (2,4,8,16) for n in range(1,w+1))
    assert paired_tile(F(1),22*reservoir/64)
    assert paired_tile(22*reservoir/32,16*reservoir/32)
    assert paired_tile((odd_even+5*odd_odd)/32,odd_even/32)
    assert all(paired_tile(odd_even/w,odd_even/w) for w in (16,8,4,2))
    assert paired_tile(odd_even,odd_even/2)
    g=(0,1,3,2,5,4,6,7)
    template_coords=layout(g)
    ranks=[0,8,12,14,15]
    assert sum(1<<i for i in ranks)==53505
    reflected=[15-i for i in ranks]
    missing_top=16-len(set(ranks+reflected))
    assert missing_top==8
    rows=node_ledger(template_coords,ranks)
    subtree=sum(row["score"] for row in rows)
    assert subtree==57
    coeff=subtree+len(ranks)*(20*missing_top-32-64)
    assert coeff==377
    images=[]
    for b in range(0,16,2):
        u=(2*b+1)%16
        physical=[(u*y+b)%16 for y in template_coords]
        hs=[h for h in automorphisms(8) if layout(h)==physical]
        assert len(hs)==1 and sum(row["score"] for row in node_ledger(physical,ranks))==57
        images.append(dict(g=hs[0],multiplier=u,translation=b))
    reservoir_score=-256-32*6+86
    assert reservoir_score==-362
    margin=odd_odd*coeff+reservoir*reservoir_score-65*odd_even
    assert margin==F(14,11)
    return {"dense_six":dense_six(),"uniform_rejected_pairs":gate,"template_physical":template_coords,
            "physical_support":sorted(template_coords[i] for i in ranks),"canonical_ranks":ranks,
            "eight_affine_cases":images,"odd_odd_ledger":rows,"odd_parent_missing":missing_top,
            "weighted_threshold_margin":str(margin)}


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    path=Path(__file__).with_name("results.json")
    output=json.dumps(run(),indent=2)+"\n"
    if parser.parse_args().check:
        assert output==path.read_text()
    else:
        path.write_text(output)
    print("8 reciprocal layouts; 8 dense pairings; threshold margin 14/11.")


if __name__=="__main__":
    main()
