"""Exact controls for block aggregation. The rows are synthetic, not Hermitian data."""
import json
from fractions import Fraction
from pathlib import Path


def order(t, p):
    if t <= 0:
        raise ValueError("positive integer required")
    result = 0
    while t % p == 0:
        result += 1
        t //= p
    return result


def block_values(t, rows):
    blocks = {}
    for prime, sequence in rows:
        blocks[prime] = blocks.get(prime, Fraction(1)) * sequence(order(t, prime))
    return blocks


def product(values):
    result = Fraction(1)
    for value in values:
        result *= value
    return result


def run():
    same = [(2, lambda k: Fraction(1, 2**k)), (2, lambda k: Fraction(2**k))]
    distinct = [(2, same[0][1]), (3, same[1][1])]
    slow = [(2, lambda k: Fraction(1, max(1, k - 11)))]
    dyadic = [(2, lambda k: 1 - Fraction(1, 4 * 16**k))]
    models = {"same_prime": same, "distinct_primes": distinct, "late_decay": slow,
              "six_square_formula_control": dyadic}
    limit, depth = 4096, 24
    report = {"scope": "synthetic product tests with exact rational arithmetic",
              "integer_panel": [1, limit], "isolated_shells": [0, depth], "models": {}}
    for name, rows in models.items():
        primes = sorted({p for p, _ in rows})
        base = block_values(1, rows)
        value = lambda t: product(block_values(t, rows).values())
        min_t = min(range(1, limit + 1), key=value)
        for t in range(1, limit + 1):
            f = block_values(t, rows)
            for p in primes:
                assert f[p] == block_values(p**order(t, p), rows)[p]
        for p in primes:
            for k in range(depth + 1):
                test = block_values(p**k, rows)
                assert all(test[q] == base[q] for q in primes if q != p)
        report["models"][name] = {
            "minimum_integer": min_t, "minimum": str(value(min_t)),
            "diagonal_at_depth_24": str(value(product(primes)**depth)),
            "isolated_at_depth_24": {str(p): str(value(p**depth)) for p in primes},
            "block_identity_checks": limit * len(primes),
            "isolating_vectors_checked": (depth + 1) * len(primes)}
    assert report["models"]["same_prime"]["minimum"] == "1"
    assert report["models"]["distinct_primes"]["minimum"] == "1/4096"
    assert report["models"]["distinct_primes"]["diagonal_at_depth_24"] == "1"
    assert report["models"]["late_decay"]["minimum"] == "1"
    assert report["models"]["late_decay"]["isolated_at_depth_24"]["2"] == "1/13"
    assert report["models"]["six_square_formula_control"]["minimum"] == "3/4"
    # Zero shells before two separate prime thresholds, including repeated places over 2.
    support_rows = [(2, lambda k: Fraction(0) if k < 1 else Fraction(3, 4)),
                    (2, lambda k: Fraction(0) if k < 2 else 1 + Fraction(1, k)),
                    (3, lambda k: Fraction(0) if k < 1 else Fraction(2, 3))]
    first, matches = None, 0
    for t in range(1, limit + 1):
        mass = product(block_values(t, support_rows).values())
        assert (mass > 0) == (t % 12 == 0)
        if mass > 0:
            first = t if first is None else first
            matches += 1
            assert mass >= Fraction(1, 2)
    assert first == 12 and matches == 341
    report["threshold_control"] = {"shell_thresholds": [[2, 1], [2, 2], [3, 1]],
                                  "least_generator": first, "positive_dilations": matches,
                                  "tested_dilations": limit, "uniform_lower_bound": "1/2"}
    return report


if __name__ == "__main__":
    data = run()
    print(json.dumps(data, indent=2))
