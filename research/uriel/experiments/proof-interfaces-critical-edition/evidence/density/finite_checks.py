"""Exact finite controls for the Gaussian split and the six-square tube at four."""

from collections import Counter
from fractions import Fraction
from itertools import product
import json


def census(depth):
    m, n = 2**((depth+1)//2), 2**(depth//2)
    q = m*n
    residues = list(product(range(m), range(n)))
    squares = Counter(((a*a+2*b*b) % m, (2*a*b) % n) for a, b in residues)
    triples = Counter({(0, 0): 1})
    for _ in range(3):
        following = Counter()
        for (a, b), l in triples.items():
            for (x, y), r in squares.items():
                following[(a+x) % m, (b+y) % n] += l*r
        triples = following
    assert sum(triples.values()) == q**3

    def count_at(a, b):
        return sum(k*triples[(a-x) % m, (b-y) % n] for (x, y), k in triples.items())

    count = count_at(4, 0)
    ratio = Fraction(count, q**5)
    companion = count_at(4, 4)
    return dict(depth=depth, q=q, count=count, companion_count=companion,
                input_cells=q**6, scalar_ball=str(Fraction(1, q)),
                split_skew_ball=str(Fraction(2, q)), tube=str(Fraction(count, q**6)),
                scalar_average=str(ratio), split_average=str(ratio/2))


def split_census(r, shear):
    m = 2**r
    mod = lambda a, b: (a % m, b % m)
    coeff = list(product(range(m), repeat=2))
    # On Gaussian input (a,b), the inverse split sends it to (2a,b-2shear*a).
    # This integral inverse descends to the finite quotient even when division by 2 does not.
    image = Counter((mod(2*x, 2*y), mod(u-2*shear*x, v-2*shear*y))
                    for (x,y), (u,v) in product(coeff, repeat=2))
    assert set(image.values()) == {4}
    assert len(image)*4 == len(coeff)**2
    return dict(coefficient_depth=r, shear=shear, domain=len(coeff)**2,
                image=len(image), multiplicity=4)


def main():
    rows = [census(d) for d in range(4, 11)]
    by_depth = {row["depth"]: row for row in rows}
    assert by_depth[5]["scalar_average"] == "2"
    at_four = by_depth[6]
    assert at_four["count"] == 2155872256 and at_four["companion_count"] == 2139095040
    assert at_four["count"] + at_four["companion_count"] == 64*by_depth[5]["count"]
    assert at_four["tube"] == "257/8192"
    assert all(row["split_average"] == "257/256" for row in rows if row["depth"] >= 6)
    rejected = dict(reverse_target_factor=str(Fraction(257,128)*2),
                    wrong_single_binary_index=2, actual_binary_index=4,
                    predecessor_as_stable=by_depth[5]["split_average"])
    assert rejected["reverse_target_factor"] != at_four["split_average"]
    assert rejected["predecessor_as_stable"] != at_four["split_average"]
    print(json.dumps(dict(balls=rows, splits=[split_census(r,s) for r in (1,2,3)
                     for s in (0,1,3)], rejected_controls=rejected), indent=2))


if __name__ == "__main__":
    main()
