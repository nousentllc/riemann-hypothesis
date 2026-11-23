"""Exact finite support and grid bounds, with a numerical geometric-series check."""
import argparse
from cmath import exp
from fractions import Fraction as F
from itertools import product
from math import pi
from pathlib import Path
from random import Random
import json


def geometry(weights, labels):
    n, total = len(weights), sum(weights)
    cap = F(max(weights) * n, total)
    # Each homogeneous positive leaf still has all its deeper first-step edges.
    charge = F(1, 2*n)
    recovered = F(0)
    depth_weight = 1
    while depth_weight < n:
        step = depth_weight
        for coset in range(step):
            points = range(coset, n, step)
            base = min(points, key=labels.__getitem__)
            cy = [(base+j*step) % n for j in range(n//step)]
            even = [s for s in cy[::2] if weights[s]]
            odd = [s for s in cy[1::2] if weights[s]]
            if not even and odd:
                return None
            m = len(cy)//2
            odd_mass = F(sum(weights[s] for s in odd), total)
            piece = odd_mass / (2*step)
            charge += piece
            if not odd:
                continue
            covered = sum(any(weights[(s+h)%n] for s in even+odd)
                          for h in range(step, n, 2*step))
            assert covered >= max(len(even), len(odd))
            recovered += piece * F(m-covered,m)
        depth_weight *= 2
    assert 0 <= recovered <= charge * (1-1/cap)
    return recovered/charge


def subset_panels():
    rng = Random(77)
    n=8
    permutations = [list(range(n)),list(reversed(range(n)))]
    for _ in range(2):
        labels=list(range(n))
        rng.shuffle(labels)
        permutations.append(labels)
    valid=invalid=0
    for labels in permutations:
        for mask in range(1,2**n):
            weights=[(mask>>i)&1 for i in range(n)]
            value=geometry(weights,labels)
            valid += value is not None
            invalid += value is None
    weighted=0
    for n in (4,8,16):
        for _ in range(64):
            weights=[rng.randrange(1,7) for _ in range(n)]
            if len(set(weights)) == 1:
                weights[0] += 1
            labels=list(range(n))
            assert geometry(weights,labels) == 0
            rng.shuffle(labels)
            assert geometry(weights,labels) == 0
            weighted += 2
    assert geometry([0,1],[0,1]) is None
    # At generator d=-1 on the eight-cycle, 1->0 is the sole direction.
    tops={0,1}
    assert 7 not in tops and (1+7)%8 in tops
    pair_checks=0
    for m in (1,2,4,8):
        full=(1<<m)-1
        for e in range(1,1<<m):
            for o in range(1,1<<m):
                covered=0
                for r in range(m):
                    shifted=((o >> r)|(o << (m-r)))&full
                    if e & shifted:
                        covered |= (1<<r)|(1<<(m-1-r))
                a,b=e.bit_count(),o.bit_count()
                assert covered.bit_count() >= max(a,b,min(m,2*min(a,b)))
                pair_checks+=1
    return dict(compatible_binary=valid,rejected_no_even=invalid,
                weighted_panels=weighted,two_orientation_pairs=pair_checks)


def near(v, order, width):
    residue = v % order
    return min(residue,order-residue) <= order*width


def resonances():
    matrices = ((1,0,0,1),(1,1,1,-1),(2,0,0,4),(3,2,1,3),(1,4,2,1))
    checks=missed_naive=0
    smallest_bound_slack=None
    for order,width in product((4,8,16,32),(F(1,16),F(1,8),F(1,4))):
        ball=sum(near(v,order,width) for v in range(order))
        for a,b,c,d in matrices:
            det=abs(a*d-b*c)
            actual=sum(near(a*i+b*j,order,width) and near(c*i+d*j,order,width)
                       for i,j in product(range(order),repeat=2))
            slack=det*ball**2-actual
            assert slack>=0
            smallest_bound_slack=slack if smallest_bound_slack is None else min(smallest_bound_slack,slack)
            checks+=1
        # Dependent rows (1,0), (1,0) give this exact resonance count.
        missed_naive += order*ball > ball**2
    return dict(independent=checks,lower_slack=smallest_bound_slack,
                rank_one_counterexamples=missed_naive)


def cell_sums():
    checks=stationary=0
    max_excess=0.0
    for phase,length,parity in product(range(1,64),(5,10,23,57),(0,1)):
        idx=list(range(parity,length,2))
        y=2*phase % 64
        z=sum(exp(2j*pi*t*phase/64) for t in idx) / len(idx)
        d=min(y,64-y)/64
        bound=1.0 if d==0 else min(1.0,1/(2*len(idx)*d))
        assert abs(z) <= bound+2e-14
        checks+=1
        stationary+=d==0
        max_excess=max(max_excess,abs(z)-bound)
    return dict(checked=checks,exact_stationary=stationary,
                tolerance="2e-14",within_tolerance=max_excess<=2e-14)


def dimensions():
    r=2049
    # For eps=1/64, u^(-r/2)=O(x^(-r/1024)).
    assert F(r,1024) > 2
    rows=[]
    for d in (2**16,2**20,2**24):
        B=16*(d+2)
        K=B**4
        kbits=(2*K+1).bit_length()
        inverse_tolerance_bits=7+r*kbits
        union_bits=(d*kbits+4).bit_length()
        translate_bits=3+2*inverse_tolerance_bits+union_bits
        # side length 1/8 gives difference box side 1/4.
        eta_bits=2*translate_bits-2*d
        # Tail <= 2*4^(d-1)*B^(-2d-3) < .001.
        assert 1+2*(d-1)-(2*d+3)*(B.bit_length()-1)<-10
        rows.append(dict(d=d,r=r,log2_M=translate_bits,log2_volume_bound=eta_bits))
    assert rows[0]["log2_volume_bound"]>0 and rows[1]["log2_volume_bound"]<0
    return rows


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--check",action="store_true")
    check=p.parse_args().check
    record=dict(finite_template=subset_panels(),independent_grids=resonances(),
                doubled_phase_cells=cell_sums(),dimension_certificates=dimensions())
    target=Path(__file__).with_name("results.json")
    serial=json.dumps(record,indent=2)+"\n"
    if check:
        assert target.read_text()==serial
    else:
        target.write_text(serial)
    print(serial)


if __name__=="__main__":
    main()
