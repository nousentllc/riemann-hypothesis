"""Verify the two children of the depth-five cell using integer character sums."""
from fractions import Fraction
from itertools import product
from collections import Counter
import json


def cyclic_product(left, right):
    return [sum(left[j] * right[(x-j) % 8] for j in range(8)) for x in range(8)]


def certificate():
    squares = Counter(((a*a + 2*b*b) % 8, (a*b) % 4)
                      for a, b in product(range(8), repeat=2))
    types = [(0, 0), (1, 0), (1, 2), (2, 0), (3, 1), (3, 3), (4, 0), (6, 2)]
    assert squares == Counter({pair: 8 for pair in types})
    # Symmetry of the odd exponents makes the evaluations at i and -i real.
    assert all(squares[x, 1] == squares[x, 3] for x in range(8))
    characters = {"one": (1, 1, 1, 1), "minus_one": (1, -1, 1, -1),
                  "real_at_i": (1, 0, -1, 0)}
    rows = {}
    for name, weights in characters.items():
        polynomial = [sum(weights[y] for x0, y in types if x0 == x) for x in range(8)]
        cube = cyclic_product(cyclic_product(polynomial, polynomial), polynomial)
        rows[name] = dict(polynomial=polynomial, cube=cube, target=cyclic_product(cube, cube)[4])
    common = Fraction(rows["one"]["target"] + rows["minus_one"]["target"], 2)
    bias = rows["real_at_i"]["target"]
    assert (common, bias) == (16384, 64)
    totals = [Fraction(8**6) * (common + sign*bias) / 2 for sign in (1, -1)]
    assert all(v.denominator == 1 for v in totals)
    assert totals == [2155872256, 2139095040]
    return dict(square_types=types, multiplicity=8, characters=rows,
                children=list(map(int, totals)), conditional_shares=[str(v/sum(totals)) for v in totals])


if __name__ == "__main__":
    print(json.dumps(certificate(), indent=2))
