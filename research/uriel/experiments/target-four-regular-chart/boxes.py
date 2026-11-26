"""Original-coordinate exact counts. Precision counts powers of 2 in each coefficient."""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
import json


def square(x, modulus):
    a, b = x
    return (a*a + 2*b*b) % modulus, (2*a*b) % modulus


@lru_cache(None)
def histogram(depth, width, center):
    modulus = 2**depth
    step = 2**width
    assert depth >= width
    return Counter(square((a, b), modulus)
                   for a in range(center[0] % step, modulus, step)
                   for b in range(center[1] % step, modulus, step))


def count_box(depth, entries, target):
    modulus = 2**depth
    counts = Counter({(0, 0): 1})
    for width, center in entries:
        after = Counter()
        for (x, y), ways in counts.items():
            for (u, v), multiplicity in histogram(depth, width, center).items():
                after[((x+u) % modulus, (y+v) % modulus)] += ways*multiplicity
        counts = after
    assert sum(counts.values()) == 4**sum(depth-width for width, _ in entries)
    n = counts[(target[0] % modulus, target[1] % modulus)]
    scalar = Fraction(n, 4**(5*depth))
    return dict(depth=depth, count=n, scalar=str(scalar), split=str(scalar/2))


def child_census():
    # At precision six every lift of a depth-four vector child has the same square sum.
    bits = list(product(range(2), repeat=2))
    hits = Counter()
    pivot_hits = Counter()
    for six in product(bits, repeat=6):
        actual = [(2*(j == 0)+8*a, 8*b) for j, (a, b) in enumerate(six)]
        squares = [square(x, 64) for x in actual]
        target = tuple(sum(v[j] for v in squares) % 64 for j in (0, 1))
        hits[target] += 1
        if target == (4, 0):
            pivot_hits[six[0]] += 1
    assert len(hits) == 4 and set(hits.values()) == {4**5}
    assert pivot_hits == {(0, 0): 4**5}
    return {'children': 4**6, 'by_residue': [[*k, v] for k, v in sorted(hits.items())],
            'pivot_classes_at_four': [[*k, v] for k, v in sorted(pivot_hits.items())]}


def run():
    zero = (0, 0)
    specs = {
        'parent': [(3, (2, 0))] + [(3, zero)]*5,
        'center_child': [(4, (2, 0))] + [(4, zero)]*5,
        'translated_transverse_child': [(4, (2, 0)), (4, (8, 8))] + [(4, zero)]*4,
        'miss_at_four': [(4, (10, 0))] + [(4, zero)]*5,
        'one_transverse_restriction': [(3, (2, 0)), (4, (8, 0))] + [(3, zero)]*4,
    }
    targets = [(4, 0), (36, 0), (4, 32), (36, 32)]
    rows = {}
    for name, entries in specs.items():
        for target in targets:
            key = name + '_at_' + '_'.join(map(str, target))
            data = [count_box(d, entries, target) for d in range(4, 9)]
            expected = Fraction(16,4**sum(d for d, _ in entries[1:]))
            if entries[0][0] == 4:
                x, y = entries[0][1]
                if square((x, y), 64) != (target[0] % 64, target[1] % 64):
                    expected = Fraction(0)
            for row in data:
                if row['depth'] >= entries[0][0]+2:
                    assert Fraction(row['scalar']) == expected
            rows[key] = data
    # Deliberately coarse observation cannot identify an empty child.
    assert Fraction(rows['miss_at_four_at_4_0'][1]['scalar']) > 0
    assert rows['miss_at_four_at_4_0'][2]['count'] == 0
    return {'precision':'coefficient depth d, target congruence modulo 2^d O',
            'source_cells_per_full_space':'4^(6d)', 'direct_counts':rows,
            'child_census':child_census()}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
