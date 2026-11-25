"""Exact checks on Z_2[sqrt(2)]/(sqrt(2)^r). Uses only the standard library."""
from collections import Counter
from fractions import Fraction
from itertools import product
import json


def moduli(depth):
    return 1 << ((depth + 1) // 2), 1 << (depth // 2)


def counts(depth, dimension, divisible=False):
    a_mod, b_mod = moduli(depth)
    squares = Counter(((a*a + 2*b*b) % a_mod, 2*a*b % b_mod)
                      for a in range(0, a_mod, 2 if divisible else 1)
                      for b in range(b_mod))
    histogram = {(0, 0): 1}
    for _ in range(dimension):
        updated = Counter()
        for (a, b), n in histogram.items():
            for (c, d), m in squares.items():
                updated[((a+c) % a_mod, (b+d) % b_mod)] += n*m
        histogram = updated
    return histogram


def direct(depth, dimension):
    a_mod, b_mod = moduli(depth)
    ring = list(product(range(a_mod), range(b_mod)))
    total, primitive = Counter(), Counter()
    for xs in product(ring, repeat=dimension):
        value = (sum(a*a+2*b*b for a,b in xs) % a_mod,
                 sum(2*a*b for a,b in xs) % b_mod)
        total[value] += 1
        if any(a % 2 for a,b in xs):
            primitive[value] += 1
    return total, primitive


def run(dimension):
    totals = []
    primitive_rows = []
    per_depth = []
    predicted_lifts = 0
    samples = {'zero':(0,0), 'one':(1,0), 'uniformizer':(0,1),
               'one_plus_uniformizer':(1,1), 'two':(2,0),
               'four':(4,0), 'sixteen':(16,0)}
    for depth in range(11):
        a_mod, b_mod = moduli(depth)
        total = counts(depth, dimension)
        totals.append(total)
        if depth == 0:
            primitive_rows.append({})
            continue
        inner = counts(depth, dimension, divisible=True)
        prim = total - inner
        assert sum(total.values()) == 2**(depth*dimension)
        assert sum(inner.values()) == 2**((depth-1)*dimension)
        assert sum(prim.values()) + sum(inner.values()) == sum(total.values())
        if depth <= 2:
            assert (total, prim) == direct(depth, dimension)
        last_a, last_b = moduli(depth-1)
        denominator = 2**(depth*(dimension-1))
        density = {t: Fraction(prim[t],denominator)
                   for t in product(range(a_mod),range(b_mod))}
        primitive_rows.append(density)
        grouped = Counter()
        for (a,b),n in total.items():
            grouped[(a % last_a,b % last_b)] += n
        assert grouped == {t:2**dimension*n for t,n in totals[-2].items()}
        if depth >= 2:
            assert total[0,1] == total[1,1] == 0
            for (a,b) in density:
                expected = (2**dimension * totals[depth-2][a//2,b//2]
                            if a%2==b%2==0 else 0)
                assert inner[a,b] == expected
        if depth > 5:
            base_a,base_b = moduli(5)
            for (a,b),value in density.items():
                assert value == primitive_rows[5][a%base_a,b%base_b]
                predicted_lifts += 1
        per_depth.append(dict(depth=depth,
            total={s:str(Fraction(total[a%a_mod,b%b_mod],denominator))
                   for s,(a,b) in samples.items()},
            primitive={s:str(density[a%a_mod,b%b_mod]) for s,(a,b) in samples.items()}))
    distinguish = {}
    base_a,base_b = moduli(4)
    for (a,b),value in primitive_rows[5].items():
        older = primitive_rows[4][a % base_a,b % base_b]
        if value != older:
            distinguish[str((a,b))] = [str(older),str(value)]
    return dict(dimension=dimension, primitive_lift_comparisons=predicted_lifts,
                depth_four_disagreements=distinguish, rows=per_depth)


def finite_certificate(dimension):
    """Second encoding of O/(pi^5), using five binary uniformizer digits."""
    depth = 5
    mask = 2**depth - 1

    def plus(x, y):
        while y:
            carry = ((x & y) << 2) & mask  # two pi^j digits give pi^(j+2)
            x, y = x ^ y, carry
        return x

    def square(x):
        value = 0
        for j in range(depth):
            if x & (1 << j):
                value = plus(value, (x << j) & mask)
        return value

    def pairs(digits):
        sub = Counter()
        for xs in product(digits, repeat=dimension//2):
            value = 0
            for x in xs:
                value = plus(value, sq[x])
            sub[value] += 1
        joined = Counter()
        for x, n in sub.items():
            for y, m in sub.items():
                joined[plus(x,y)] += n*m
        return joined

    sq = [square(x) for x in range(mask+1)]
    all_vectors = pairs(range(mask+1))
    inner_vectors = pairs(range(0,mask+1,2))
    def coords(x):
        a = sum(((x >> j) & 1) << (j//2) for j in range(0,depth,2))
        b = sum(((x >> j) & 1) << (j//2) for j in range(1,depth,2))
        return a,b
    for expected, observed in ((counts(depth,dimension),all_vectors),
                               (counts(depth,dimension,True),inner_vectors)):
        assert all(expected[coords(x)] == observed[x] for x in range(mask+1))
    return 2*(mask+1)


def check_controls(rows):
    by_rank = {x['dimension']:x for x in rows}
    for rank,record in by_rank.items():
        record['independent_depth_five_bin_counts'] = finite_certificate(rank)
    four = by_rank[4]['rows']
    for row in four[4:]:
        assert row['total']['one'] == row['total']['two'] == '2'
        assert row['total']['four'] == '9/4'
    six = by_rank[6]['rows']
    for k in range(1,3):
        label = {1:'four',2:'sixteen'}[k]
        for row in six[4*k+1:]:
            assert Fraction(row['total'][label]) == 2+Fraction(2,256**k)
    for row in six[4:]:
        assert row['total']['one'] == '2' and row['primitive']['zero'] == '15/8'


if __name__ == '__main__':
    results = [run(4),run(6)]
    check_controls(results)
    print(json.dumps(results,indent=2))
