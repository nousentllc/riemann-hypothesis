"""Exact all-address tests at small depths and independent square-class controls."""

from collections import Counter
from fractions import Fraction
import json

from companion_counts import count, density, six_square_histogram


def shell(depth, k):
    """Every visible target class on the shell at this uniformizer depth."""
    real_mod, pi_mod, histogram = six_square_histogram(depth)
    scale = 4**k
    result = Counter()
    for a in range(1, real_mod // scale, 2):
        for b in range(pi_mod // scale):
            observed = Fraction(histogram[(scale*a, scale*b)], 2**(5*depth))
            increment = Fraction(2, 256**k)
            if depth == 4*k+1:
                assert observed == 2
                branch = "unresolved"
            elif b % 2 == 0:
                assert observed == 2+increment
                branch = "even"
            else:
                assert observed == 2-increment
                branch = "odd"
            result[branch, str(observed)] += 1
    assert sum(result.values()) == 2**(depth-4*k-1)
    return {
        "k": k, "uniformizer_depth": depth,
        "bins": [
            {"coefficient_class": branch, "ratio": ratio, "target_bins": n}
            for (branch, ratio), n in sorted(result.items())
        ],
    }


def main():
    shells = [
        shell(d, k)
        for k, depths in ((1, range(5, 11)), (2, range(9, 13)), (3, range(13, 15)))
        for d in depths
    ]
    anchors = []
    for depth, step, base, expected in (
        (4, 2, 1, 2_097_152),
        (6, 2, 1, 2_147_483_648),
        (6, 4, 2, 2_281_701_376),
    ):
        mod = 2**(depth//2)
        addresses = [(a, b) for a in range(base, mod, step) for b in range(0, mod, step)]
        for a, b in addresses:
            assert count(depth, a, b) == expected
        anchors.append({
            "coefficient_modulus": mod, "base": base,
            "step": step, "target_bins": len(addresses), "raw_count_per_bin": expected,
        })

    squares_mod_four = sorted({
        ((a*a + 2*b*b) % 4, 2*a*b % 4) for a in range(1, 4, 2) for b in range(4)
    })
    assert (1, 2) not in squares_mod_four
    nonsquare_same_density = density(10, 4, 8)
    assert nonsquare_same_density == density(10, 4, 0) == Fraction(257, 128)
    print(json.dumps({
        "shells": shells, "anchor_counts": anchors,
        "unit_squares_mod_four": squares_mod_four,
        "positive_nonsquare_control": {
            "unit": [1, 2], "uniformizer_depth": 10,
            "ratio": str(nonsquare_same_density),
        },
    }, indent=2))


if __name__ == "__main__":
    main()
