"""Exact controls for rank limits, scale limits and counts after compression."""

from collections import Counter
from fractions import Fraction
from math import isqrt
import json


def prime(n):
    return n >= 2 and all(n % p for p in range(2, isqrt(n) + 1))


def host_hyp(q, d):
    return prime(q) and prime(d) and q % 8 == 3 and d % 16 == 7 and pow(-d, (q-1)//2, q) == 1


def rank_control(d):
    rows = []
    # t >= r+5 makes 4*r*r < d, so this finite search covers the rank envelope.
    for r in range(1, isqrt(d//4) + 1):
        for m in range(2, r + 1, 2):
            k = r + 1 - m
            if k % 2 or k < m + 3:
                continue
            least = max(r + 5, 3*m + 1)
            t = least if least % 2 else least + 1
            for t in range(t, (d - 2)//(4*r) + 1, 2):
                rows.append((k, m, r, t))
    best = max(rows, key=lambda x:x[0])
    assert max(row[2] for row in rows) == 45 and best[:3] == (44,2,45)
    threshold=min(4*r*t+1 for k,m,r,t in rows)
    assert threshold==365
    qs=[q for q in range(threshold+1,d) if host_hyp(q,d)]
    assert qs and host_hyp(11,d) and 11 < threshold
    return dict(scalar_rank_quadruples=len(rows), largest_k_witness=best,
                max_r=45, weakest_aux_prime_threshold=threshold,
                first_larger_prime_passing_weak_tests=qs[0])


def record(selected_outputs):
    unsigned = {a for _, a in selected_outputs}
    counts = Counter(a % 2 for _, a in selected_outputs)
    distinct_counts = Counter(a % 2 for a in unsigned)
    return dict(
        total=len(selected_outputs),
        distinct_signed=len(set(selected_outputs)),
        distinct_unsigned=len(unsigned),
        raw_counts=[counts[i] for i in range(2)],
        source_parity_coefficient=str(Fraction(counts[0]-counts[1],len(selected_outputs))),
        image_parity_coefficient=str(Fraction(distinct_counts[0]-distinct_counts[1],len(unsigned))),
        image_counts=[distinct_counts[i] for i in range(2)],
        source_shares=[str(Fraction(counts[i],len(selected_outputs))) for i in range(2)],
        image_shares=[str(Fraction(distinct_counts[i],len(unsigned))) for i in range(2)],
    )


def compression_controls():
    # A = Z/8, A0 = <2>, TT = {0,...,6}.  All data are synthetic.
    outputs=[(1,i) for i in range(7)]
    balanced=record(outputs * 100)
    uneven=record(outputs * 100 + [(1,0)])
    assert balanced['source_shares']==balanced['image_shares']==['4/7','3/7']
    assert uneven['source_shares']!=uneven['image_shares']
    assert balanced['source_parity_coefficient']=='1/7'
    assert Fraction(uneven['source_parity_coefficient'])-Fraction(1,7)==Fraction(6,4907)
    assert balanced['raw_counts']==[400,300]
    assert balanced['image_counts']==[4,3]
    # A variable number of signs can itself change image shares before multiplicities are counted.
    two_signs=record([(1,0),(-1,0),(1,1)])
    assert two_signs['source_shares']==['2/3','1/3']
    assert two_signs['image_shares']==['1/2','1/2']
    return dict(balanced=balanced, uneven=uneven, two_signs=two_signs)


def quota_controls():
    feasible = []
    tested = 0
    closest = None
    for n0 in (1, 2, 4, 8, 16):
        for o in range(1, 22//n0+1):
            totals = []
            for n in range(1, n0*o+1):
                tested += 1
                weights = [Fraction(4, 3*o+1)] + [Fraction(3, 3*o+1)]*(o-1)
                desired = [w*n for w in weights]
                if all(x.denominator==1 and x<=n0 for x in desired):
                    totals.append(n)
                for w in set(weights):
                    for c in range(min(n0, n)+1):
                        gap = abs(Fraction(c,n)-w)
                        if gap:
                            assert gap >= Fraction(1,n*(3*o+1))
                            closest = gap if closest is None else min(closest,gap)
            assert bool(totals) == (o == 1 or n0 >= 4)
            if o > 1 and totals:
                assert all(n % (3*o+1) == 0 for n in totals)
                feasible.append(dict(cosets=o, subgroup_size=n0, exact_totals=totals))
    return dict(size_trials=tested, nontrivial_exact_profiles=feasible,
                smallest_positive_grid_gap=str(closest))


def main():
    lower=2**1071
    assert lower>44 and (lower+43)//44>10**320
    print(json.dumps(dict(
        q0=18480,d=9239,q_11_satisfies_weak_conditions=host_hyp(11,9239),
        rank=rank_control(9239),
        lower_bound_decimal_digits=len(str(lower)),
        minimum_max_signed_fiber_decimal_digits=len(str((lower+43)//44)),
        projected_counts=compression_controls(), abstract_quotas=quota_controls()),indent=2))


if __name__=='__main__':
    main()
