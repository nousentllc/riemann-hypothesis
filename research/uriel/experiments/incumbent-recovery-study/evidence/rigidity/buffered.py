"""Audit buffered residue classes, dyadic rank scores and the finite-law comparison."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from pathlib import Path
import argparse
import json
import random
from geometry import orbits


def check_geometry():
    counts=Counter()
    for n in (32,64,128):
        for seed in range(-1,17):
            rank=list(range(n))
            if seed>=0:
                random.Random(seed).shuffle(rank)
            earliest=min(range(n),key=rank.__getitem__)
            parity=earliest%2
            E={t for t in range(n) if t%2==parity}
            B=set(range(n))-E
            b=min(B,key=rank.__getitem__)
            c=min((t for t in B if (t-b)%4), key=rank.__getitem__)
            leaves={b%16,c%16}
            g=[F(3,2) if t in E else F(2) if t%16 in leaves else F(0) for t in range(n)]
            assert sum(g)==n
            odd_visits=[0]*n
            isolated_mass=F(0)
            for h in range(1,n):
                for cyc in orbits(n,h,rank):
                    vals=[g[t] for t in cyc]
                    if not any(vals):
                        continue
                    L=len(cyc)
                    for t in cyc[1::2]:
                        odd_visits[t]+=1
                    if h%2:
                        case="whole"
                        expected=(1,F(3,4))
                    elif cyc[0] in E:
                        case="reservoir"
                        expected=(F(3,2),F(3,4))
                    elif h%4:
                        case="split_root"
                        expected=(F(1,2),F(1,4))
                    elif h%8:
                        case="split_child"
                        expected=(F(1,2),F(1,2))
                    elif h%16:
                        case="split_grandchild"
                        expected=(1,1)
                    else:
                        case="full_leaf"
                        expected=(2,1)
                    assert (sum(vals)/L,sum(vals[::2])/L)==expected
                    directed=[sum(vals[i]>0 and vals[(i+1)%L]>0 for i in range(bit,L,2)) for bit in (0,1)]
                    is_hole=case=="split_root" and h%16 in {(3*(c-b))%16,(-3*(c-b))%16}
                    if is_hole:
                        assert sum(directed)==0
                        isolated_mass+=sum(vals[1::2])
                    elif sum(vals[1::2])>0:
                        assert max(directed)>=L/16
                    counts[case]+=1
            assert isolated_mass/(2*n*n)==F(1,128)
            Emean=F(sum(odd_visits[t] for t in E),n*len(E))
            assert Emean==F(1,4)-F(1,2*n)
            leaf_points=[t for t in B if t%16 in leaves]
            Bmean=F(sum(odd_visits[t] for t in leaf_points),n*len(leaf_points))
            assert Bmean==F(21,32)-F(1,2*n)
            k=sum(g[t]*odd_visits[t] for t in range(n))/(2*n*n)
            assert k==F(45,256)-F(1,4*n)
    return dict(label_instances=54,orbits_by_type=dict(counts),hole_share="1/128",
                finite_normalized_exposure="45/256 - 1/(4n)")


def falling(a,r):
    v=1
    for j in range(r):
        v*=a-j
    return v


def check_pattern_cap():
    n=11
    panels=patterns=0
    max_relative=F(0)
    for k in range(1,n):
        all_sets=list(combinations(range(n),k))
        for anchor in (False,True):
            samples=[s for s in all_sets if not anchor or n-1 in s]
            M=n-int(anchor)
            K=k-int(anchor)
            p=F(K,M)
            for m in range(1,8):
                codes=Counter(tuple(int(t in s) for t in range(m)) for s in samples)
                bound=F(M**m,falling(M,m))
                for pattern in product((0,1),repeat=m):
                    i=sum(pattern)
                    empirical=F(codes[pattern],len(samples))
                    analytic=F(falling(K,i)*falling(M-K,m-i),falling(M,m))
                    iid=p**i*(1-p)**(m-i)
                    assert empirical==analytic and empirical<=bound*iid
                    if iid:
                        max_relative=max(max_relative,empirical/iid)
                    patterns+=1
                panels+=1
    return dict(population=n,panels=panels,patterns=patterns,
                largest_observed_likelihood_ratio=str(max_relative))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    check=parser.parse_args().check
    result=dict(geometry=check_geometry(),likelihood=check_pattern_cap())
    serialized=json.dumps(result,indent=2)+"\n"
    target=Path(__file__).with_name("buffered-results.json")
    if check:
        assert target.read_text()==serialized
    else:
        target.write_text(serialized)
    print(serialized)


if __name__=="__main__":
    main()
