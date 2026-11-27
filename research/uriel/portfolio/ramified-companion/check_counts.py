"""Reproduce the companion-fiber checkpoint by exact residue convolution."""

from collections import Counter
from fractions import Fraction
from functools import lru_cache
import json


@lru_cache(maxsize=None)
def six_square_histogram(depth):
    real_mod = 2 ** ((depth + 1) // 2)
    pi_mod = 2 ** (depth // 2)
    squares = Counter(
        ((a * a + 2 * b * b) % real_mod, (2 * a * b) % pi_mod)
        for a in range(real_mod)
        for b in range(pi_mod)
    )

    def convolve(left, right):
        result = Counter()
        for (a, b), left_count in left.items():
            for (c, d), right_count in right.items():
                result[(a + c) % real_mod, (b + d) % pi_mod] += left_count * right_count
        return result

    triple = convolve(convolve(squares, squares), squares)
    histogram = convolve(triple, triple)
    assert sum(histogram.values()) == 2 ** (6 * depth)
    return real_mod, pi_mod, histogram


def count(depth, real_part, pi_part):
    real_mod, pi_mod, histogram = six_square_histogram(depth)
    return histogram[real_part % real_mod, pi_part % pi_mod]


def density(depth, real_part, pi_part):
    return Fraction(count(depth, real_part, pi_part), 2 ** (5 * depth))


def main():
    rows = []
    for k, depths in ((1, range(5, 10)), (2, range(9, 11))):
        target = 4**k
        for depth in depths:
            square = density(depth, target, 0)
            companion = density(depth, target, target)
            deficit = Fraction(2, 256**k) if depth >= 4 * k + 2 else 0
            assert square == 2 + deficit and companion == 2 - deficit
            rows.append({
                "k": k,
                "depth": depth,
                "square_count": count(depth, target, 0),
                "companion_count": count(depth, target, target),
                "density_denominator": 2 ** (5 * depth),
                "square_density": str(square),
                "companion_density": str(companion),
            })

    # Dividing every coordinate by π costs a factor of 16 in density.
    depth_nine = [
        density(9, 4, 4) - density(7, 2, 2) / 16,
        density(7, 2, 2) / 16 - density(5, 1, 1) / 256,
        density(5, 1, 1) / 256,
    ]
    assert depth_nine == [Fraction(15, 8), Fraction(15, 128), 0]
    print(json.dumps({"rows": rows, "depth_nine_strata": list(map(str, depth_nine))}, indent=2))


if __name__ == "__main__":
    main()
