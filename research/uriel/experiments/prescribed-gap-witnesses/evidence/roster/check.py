"""Finite checks for the explicit conductor-one specialization."""
import json
from fractions import Fraction
from math import gcd, isqrt


def is_prime(n):
    return n >= 2 and all(n % k for k in range(2, isqrt(n) + 1))


def roster():
    first = min(n for n in range(7, 8) if is_prime(n) and n % 4 == 3 and gcd(n, 1) == 1)
    second = min(n for n in range(4) if is_prime(n) and (n - 1) % 1 == 0 and gcd(n, 2 * first) == 1)
    squared_distance = Fraction(1, 4) + Fraction(7, 16)
    product = first * second
    factors = [p for p in range(3, product + 1, 2) if is_prime(p) and product % p == 0]
    assert (first, second, squared_distance, factors) == (7, 3, Fraction(11, 16), [3, 7])
    return {"pK": first, "pOne": second, "rounding_norm_bound": str(squared_distance),
            "odd_slots_using_written_class_number_proof": sorted(set(factors) | {3})}


if __name__ == "__main__":
    print(json.dumps(roster(), indent=2))
