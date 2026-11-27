#!/usr/bin/env python3
"""Independent finite-ring controls for the unit-pivot calculation."""
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from math import gcd
from pathlib import Path

def check_patch(prime, depth):
    modulus = prime ** depth
    residues = range(modulus)
    units = [x for x in residues if gcd(x, modulus) == 1]
    counts = [0] * modulus
    shifted = [0] * modulus
    bad = [0] * modulus
    for x, t, z in product(units, residues, residues):
        counts[(x*t + z*z + 3*z + 1) % modulus] += 1
        shifted[(x*t + z*z*z + 1) % modulus] += 1
        bad[(prime*x*t + prime*z*z) % modulus] += 1
    expected = len(units) * modulus
    assert counts == shifted == [expected] * modulus
    assert all(count == (prime*expected if a % prime == 0 else 0)
               for a, count in enumerate(bad))
    return dict(p=prime, r=depth, modulus=modulus, targets=modulus,
                tested_triples_per_form=sum(counts), unit_patch_count=expected,
                normalized_patch=str(Fraction(expected, modulus**2)),
                scaled_off_image=sum(1 for count in bad if not count),
                scaled_on_image=max(bad), polynomial_offsets_tested=2)

def check_valuation_obstruction(depth):
    modulus = 3 ** depth
    counts = Counter((x*x+y*y) % modulus for x, y in product(range(modulus), repeat=2))
    return dict(p=3, r=depth, target_1=counts[1], target_3=counts[3],
                target_9=counts[9], explanation="Two squares divisible by 3 require both coordinates divisible by 3.")

def compute():
    panels = [(2,r) for r in range(1,7)] + [(3,r) for r in range(1,5)] + [(5,r) for r in range(1,4)]
    rows = [check_patch(p, r) for p, r in panels]
    binary = [check_valuation_obstruction(r) for r in range(3,6)]
    assert all(row['target_1']>0 and row['target_3']==0 and row['target_9']>0 for row in binary)
    return dict(rings=len(rows), target_ring_pairs=sum(row['targets'] for row in rows),
                triples_per_form_total=sum(row['tested_triples_per_form'] for row in rows),
                chart=rows, anisotropic_control=binary)

if __name__ == "__main__":
    print(json.dumps(compute(), indent=2, sort_keys=True))
