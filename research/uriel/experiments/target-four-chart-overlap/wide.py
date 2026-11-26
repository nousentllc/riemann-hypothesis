"""Count all six physical squares in the enlarged box using integer convolution."""
from collections import Counter
from fractions import Fraction
import json
from overlap import Ring


def square_histogram(ring, center, width):
    result = Counter()
    for value in ring.elements:
        a, b = ring.coordinates(value)
        x, y = center + width*a, width*b
        delta = x*x + 2*y*y - center*center
        cross = 2*x*y
        assert delta % 256 == cross % 256 == 0
        result[ring.pack(delta//256, cross//256)] += 1
    return result


def convolve(ring, left, right):
    result = Counter()
    for a, count_a in left.items():
        for b, count_b in right.items():
            result[ring.add(a, b)] += count_a * count_b
    return result


def count(depth):
    ring = Ring(depth)
    hist = convolve(ring, square_histogram(ring, -6, 128), square_histogram(ring, 8, 16))
    passive = square_histogram(ring, 0, 32)
    for _ in range(4):
        hist = convolve(ring, hist, passive)
    target_count = 2 * ring.size**5
    for target in ring.elements:
        real, _ = ring.coordinates(target)
        assert hist[target] == (target_count if real % 2 == 0 else 0)
    assert sum(hist.values()) == ring.size**6
    scalar_cell = Fraction(1, 4**(8+depth))
    source = Fraction(1, 4**31)
    density = source * Fraction(hist[0], ring.size**6) / scalar_cell
    assert scalar_cell * len(hist) == Fraction(1, 2**17)
    assert density == Fraction(1, 2**45)
    return dict(depth=depth, target_classes=ring.size, attained=len(hist),
                per_attained_target=target_count, missing=ring.size-len(hist),
                total_vectors=ring.size**6, scalar_density=str(density), split_density=str(density/2))


if __name__ == "__main__":
    print(json.dumps([count(d) for d in range(1, 6)], indent=2))
