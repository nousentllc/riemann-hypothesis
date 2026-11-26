"""Count target four directly in O/(pi^d), with pi^2=2. Python standard library."""
from collections import Counter
from fractions import Fraction
import json


def square_histogram(d, level):
    """One coordinate in pi^level O, with both input coefficients counted."""
    m, n = 2**((d+1)//2), 2**(d//2)
    return Counter(((a*a+2*b*b) % m, (2*a*b) % n)
                   for a in range(0, m, 2**((level+1)//2))
                   for b in range(0, n, 2**(level//2)))


def convolve(left, right, m, n):
    result = Counter()
    for (a, b), weight in left.items():
        for (c, e), count in right.items():
            result[(a+c) % m, (b+e) % n] += weight*count
    return result


def powers(hist, m, n, exponent):
    result = [Counter({(0, 0): 1})]
    for _ in range(exponent):
        result.append(convolve(result[-1], hist, m, n))
    return result


def target_coefficient(left, right, m, n):
    return sum(count * right[(4-a) % m, (-b) % n] for (a, b), count in left.items())


def census(d):
    m, n = 2**((d+1)//2), 2**(d//2)
    raw = []
    for j in range(3):
        weak = square_histogram(d, j)
        strict = square_histogram(d, j+1)
        exact = weak - strict
        assert sum(exact.values()) == 2**(d-j-1)
        before = powers(strict, m, n, 5)
        after = powers(weak, m, n, 5)
        raw.append([target_coefficient(convolve(before[i], exact, m, n), after[5-i], m, n)
                    for i in range(6)])
    unrestricted = powers(square_histogram(d, 0), m, n, 6)[6][4 % m, 0]
    assert sum(map(sum, raw)) == unrestricted
    denom = 2**(5*d)
    return dict(pi_depth=d, denominator=denom, raw=raw,
                scalar_masses=[[str(Fraction(x, denom)) for x in row] for row in raw],
                unrestricted_count=unrestricted, total=str(Fraction(unrestricted, denom)))


if __name__ == "__main__":
    print(json.dumps([census(d) for d in (8, 9, 10)], indent=2))
