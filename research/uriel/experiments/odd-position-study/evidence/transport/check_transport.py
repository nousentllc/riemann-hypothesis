"""Exact finite controls for the clip formula and the prime bulk classification."""

import itertools
import json
from fractions import Fraction as F
from math import isqrt


def primes_below(upper):
    return [n for n in range(2, upper) if all(n % k for k in range(2, isqrt(n) + 1))]


def unit_clip(b, level, threshold):
    return min(level, max(F(0), b + level - threshold))


def check_scalar():
    count = 0
    grid = [F(0), F(1, 3), F(1), F(3, 2), F(5)]
    for b, level, eta, kappa, threshold in itertools.product(grid, repeat=5):
        for extra in sorted({F(0), eta / 2, eta}):
            off = level + extra
            raw = off - kappa + min(b, threshold) - min(b + off, threshold)
            actual = max(F(0), raw)
            assert raw == unit_clip(b, off, threshold) - kappa
            proxy = unit_clip(b, level, threshold)
            assert proxy - kappa <= actual <= proxy + eta
            count += 1
    return count


def check_prime_window():
    """Fractions avoid rounding at the two cutoffs. No actual witness is supplied."""
    checked = 0
    exempt = 0
    for H, x in [(65, 7), (128, 13), (1000, 100)]:
        alpha = F(1, x**2)
        beta = F(1, 4 * x**2)
        bprime = F(10_000)
        level = bprime / x
        for p, d in itertools.product(primes_below(H), (0, 1, 3, 5)):
            for a in (H * bprime, H * bprime * (1 + alpha)):
                for b in (bprime, bprime * (1 + beta)):
                    threshold = a / p**d if d else F(0)
                    weight = unit_clip(b, level, threshold) / level
                    target = int(d != 1)
                    exceptional = p**3 <= H * (1 + alpha) or p * (1 + F(1, x) + beta) > H
                    assert 0 <= weight <= 1
                    if exceptional:
                        exempt += 1
                    else:
                        assert weight == target
                    checked += 1
    return {"configurations": checked, "inside_exceptional_strips": exempt,
            "outside_strips_matches_adjacency": checked - exempt}


def controls():
    H, x, b = 1000, 100, F(10_000)
    level = b / x
    a = H * b
    rho = F(1, x**2)
    records = []
    for p, d, expected in [(997, 1, F(697, 997)), (983, 1, 0), (983, 3, 1), (983, 0, 1)]:
        assert p in primes_below(H) and p < H * (1 - rho) and p**2 > H * (1 + rho)
        threshold = a / p**d if d else F(0)
        weight = unit_clip(b, level, threshold) / level
        assert weight == expected
        records.append({"p": p, "d": d, "fraction": str(weight)})
    # A headroom claim using only InWin is falsified for unrestricted b.
    p = 983
    no_upper_bound_b = 2 * b
    assert unit_clip(no_upper_bound_b, level, a / p) == level
    return {"H": H, "x": x, "bprime": int(b), "rho": str(rho),
            "outside_every_power_band": records,
            "unrestricted_b_control_at_p_983": "full charge when b is twice bprime"}


def main():
    print(json.dumps({"classification": "synthetic rational inequalities",
                      "scalar_cases": check_scalar(), "prime_window": check_prime_window(),
                      "controls": controls()}, indent=2))


if __name__ == "__main__":
    main()
