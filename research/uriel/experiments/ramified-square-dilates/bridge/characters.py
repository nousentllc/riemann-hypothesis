"""Exact additive-character check on Z/32[sqrt(2)], with no floating point arithmetic."""
from collections import Counter, defaultdict
from fractions import Fraction
from math import gcd
import json

MOD = 32
HALF = MOD // 2
TARGETS = {"four": (4, 0), "one": (1, 0), "two": (2, 0), "pi": (0, 1),
           "one_plus_pi": (1, 1), "two_pi": (0, 2), "four_plus_two_pi": (4, 2),
           "sixteen": (16, 0), "zero": (0, 0)}


def multiply(a, b):
    """Product of two integral degree < 16 representatives modulo X^16+1."""
    answer = [0] * HALF
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    n = i + j
                    answer[n % HALF] += x * y * (1 if n < HALF else -1)
    return answer


def histogram(primitive_coordinate_only):
    return Counter(((a*a + 2*b*b) % MOD, 2*a*b % MOD)
                   for a in range(0, MOD, 2 if primitive_coordinate_only else 1)
                   for b in range(MOD))


def spectrum(squares):
    totals = {t: defaultdict(lambda: [0]*HALF) for t in TARGETS}
    for u in range(MOD):
        for v in range(MOD):
            chars = [0] * MOD
            for (a, b), count in squares.items():
                chars[(u*a+v*b) % MOD] += count
            g = [chars[i]-chars[i+HALF] for i in range(HALF)]
            g3 = multiply(multiply(g, g), g)
            g6 = multiply(g3, g3)
            conductor = MOD // gcd(MOD, u, v)
            for label, (a, b) in TARGETS.items():
                phase = (-u*a-v*b) % MOD
                out = totals[label][conductor]
                for i, coeff in enumerate(g6):
                    j = (i+phase) % MOD
                    out[j % HALF] += coeff if j < HALF else -coeff
    result = {}
    for t, groups in totals.items():
        assert all(all(x == 0 for x in p[1:]) for p in groups.values())
        numerator = sum(p[0] for p in groups.values())
        n, r = divmod(numerator, MOD**2)
        assert r == 0
        result[t] = dict(count=n, density=str(Fraction(n, MOD**10)),
                         character_orders={str(k):str(Fraction(p[0], MOD**12))
                                           for k,p in sorted(groups.items())})
    return result


def run():
    full, even = spectrum(histogram(False)), spectrum(histogram(True))
    densities = {t: str(Fraction(full[t]['count']-even[t]['count'], MOD**10)) for t in full}
    assert full['four']['count'] == 257 * 2**43
    assert even['four']['density'] == '17/128' and densities['four'] == '15/8'
    assert full['one']['density'] == '2' and full['two']['density'] == '17/8'
    assert full['pi']['count'] == full['one_plus_pi']['count'] == 0
    assert densities['two_pi'] == '63/32' and densities['four_plus_two_pi'] == '65/32'
    for lookup in (full, even):
        for row in lookup.values():
            assert sum(map(Fraction, row['character_orders'].values())) == Fraction(row['density'])
    return dict(modulus=MOD, uniformizer_depth=10, ring_size=MOD**2,
                all=full, all_divisible_by_pi=even, primitive_density=densities)


if __name__ == '__main__':
    print(json.dumps(run(), sort_keys=True, indent=2))
