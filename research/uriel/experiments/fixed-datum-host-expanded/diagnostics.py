"""Exact finite controls for the expanded witness paper (Python standard library)."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import ceil, comb, floor, isqrt, prod
import json


def is_prime(n):
    return n >= 2 and all(n % p for p in range(2, isqrt(n) + 1))


def prime_panel():
    counts = Counter()
    examples = []
    for multiplier in range(1, 25):
        q0 = 18480 * multiplier
        tested = 0
        first = None
        for t in range(1, 100, 2):
            d = q0 // 2 * t - 1
            if not is_prime(d):
                continue
            assert 2 * (d + 1) == q0 * t and (d + 1) % q0
            assert (-d) % 11 == 1
            assert (d % 16 == 7) == (q0 % 32 != 0)
            counts[str(d % 16)] += 1
            tested += 1
            if first is None:
                first = d
        examples.append(dict(multiplier=multiplier, prime_records=tested, first=first))
    return dict(odd_multipliers_per_modulus=50, prime_residues=dict(counts), by_modulus=examples)


def discrepancy(hist):
    o, m = len(hist), sum(hist)
    w = 3 * o + 1
    return max(abs(Fraction(k, m) - Fraction(a, w)) for k, a in zip(hist, [4] + [3] * (o - 1)))


def interval_test(o, c, m, delta):
    targets = [Fraction(4, 3 * o + 1)] + [Fraction(3, 3 * o + 1)] * (o - 1)
    lower = [max(0, ceil(m * (v - delta))) for v in targets]
    upper = [min(c, floor(m * (v + delta))) for v in targets]
    return all(l <= u for l, u in zip(lower, upper)) and sum(lower) <= m <= sum(upper)


def histogram_panel(o, c):
    # Three counts: actual subsets, enumerated coset counts, and the attainable interval criterion.
    total = o * c
    histograms = list(product(range(c + 1), repeat=o))
    rows = []
    for m in range(1, total + 1):
        measured = Counter()
        for subset in combinations(range(total), m):
            counts = [0] * o
            for x in subset:
                counts[x % o] += 1
            measured[discrepancy(counts)] += 1
        predicted = Counter()
        for h in histograms:
            if sum(h) == m:
                predicted[discrepancy(h)] += prod(comb(c, v) for v in h)
        assert measured == predicted and sum(measured.values()) == comb(total, m)
        best = min(predicted)
        probes = set(predicted) | {Fraction(0)}
        for radius in list(probes):
            if radius:
                probes.add(radius - Fraction(1, 2 * m * (3 * o + 1)))
        for radius in probes:
            assert interval_test(o, c, m, radius) == (best <= radius)
        expected_exact = m % (3 * o + 1) == 0 and 4 * (m // (3 * o + 1)) <= c
        assert (best == 0) == expected_exact
        rows.append(dict(m=m, best=str(best), attaining=predicted[best], radii_checked=len(probes)))
    return dict(o=o, capacity=c, subsets=(1 << total) - 1, rows=rows)


def collision_panel():
    rows = []
    for k in range(1, 9):
        for r in range(k + 1):
            m = k + r
            # The first r image points have two antecedents; the others have one.
            multiplicities = [2] * r + [1] * (k - r)
            tv = sum(abs(Fraction(n, m) - Fraction(1, k)) for n in multiplicities) / 2
            assert tv == Fraction(r * (k - r), m * k)
            worst = max(abs(sum(Fraction(multiplicities[i], m) - Fraction(1, k)
                                for i in range(k) if mask & (1 << i))) for mask in range(1 << k))
            assert worst == tv
            rows.append(dict(k=k, r=r, m=m, discrepancy=str(worst)))
    weighted = discrepancy((4, 3))
    after = discrepancy((2, 3))
    assert weighted == 0 and after == Fraction(6, 35)
    return dict(cases=len(rows), example=dict(weighted=str(weighted), unweighted=str(after)),
                maximum=max(rows, key=lambda row: Fraction(row['discrepancy'])))


def main():
    panels = [histogram_panel(o, c) for o, c in [(2, 8), (3, 4), (4, 4), (5, 2)]]
    print(json.dumps(dict(primes=prime_panel(), coset_panels=panels,
        enumerated_subsets=sum(p['subsets'] for p in panels),
        interval_checks=sum(r['radii_checked'] for p in panels for r in p['rows']),
        two_sheet_collisions=collision_panel()), indent=2))


if __name__ == '__main__':
    main()
