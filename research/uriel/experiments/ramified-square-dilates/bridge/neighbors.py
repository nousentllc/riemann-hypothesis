"""Reproduce the target tree, the distribution of all bins and the order-eight calculation."""
from collections import Counter
from fractions import Fraction
from math import gcd
from pathlib import Path
import json
import sys

from RamBaseCertificate import counts
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'literature'))
from ramified_probe import counts as count_at_depth
from ramified_probe import moduli


def empirical_distribution():
    cells = counts()[-1]
    frequency = Counter(Fraction(cells[a, b], 2**50) for a in range(32) for b in range(32))
    expected = {Fraction(0): 512, Fraction(2): 258}
    for j in range(7):
        offset = Fraction(1, 8*4**j)
        for sign in (-1, 1):
            expected[2 + sign*offset] = 64 // (2**j)
    assert frequency == expected
    var = sum((x-2)**2 * count for x, count in frequency.items() if x) / 512
    assert var == sum(Fraction(1, 256*32**j) for j in range(7))
    return {str(x): n for x,n in sorted(frequency.items())}, str(var)


def split_tree():
    levels = []
    for r in range(2, 11):
        m, n = moduli(r)
        cells = count_at_depth(r, 6)
        denominator = 2**(5*r)
        get = lambda a,b: str(Fraction(cells[a % m, b % n], denominator))
        levels.append(dict(depth=r, four=get(4,0), sibling=get(4,4), sixteen=get(16,0)))
    return levels


def order_eight():
    classes = Counter()
    for u in range(8):
        for v in range(8):
            if gcd(8,u,v) != 1:
                continue
            hist = Counter((u*(a*a+2*b*b)+2*v*a*b) % 8 for a in range(8) for b in range(8))
            residue = tuple(hist[i]-hist[i+4] for i in range(4))
            classes[residue, (-1)**u] += 1
    assert len(classes) == 7 and sum(classes.values()) == 48
    return [dict(basis=list(values), phase=phase, count=n)
            for (values,phase),n in sorted(classes.items())]


def run():
    distribution, variance = empirical_distribution()
    return dict(coarse_distribution=distribution, conditional_variance=variance,
                tree=split_tree(), order_eight_characters=order_eight())


if __name__ == '__main__':
    print(json.dumps(run(),indent=2))
