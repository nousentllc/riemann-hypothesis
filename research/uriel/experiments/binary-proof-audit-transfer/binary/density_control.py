"""A finite CRT control for the moving-prime error in the scalar count."""
from fractions import Fraction
import json
from math import prod


def delta(n, q):
    """Signed deviation of an artificial local density on the integer residue classes."""
    return Fraction(q - 1 if n % q == 0 else -1, q**2)


def average(seq):
    return sum(seq) / len(seq)


def check(primes):
    period = prod(primes)
    values = range(1, period + 1)
    by_prime = {}
    for q in primes:
        deviations = [delta(n, q) for n in values]
        assert average(deviations) == 0
        absolute = average([abs(d) for d in deviations])
        assert absolute == Fraction(2 * (q - 1), q**3)
        by_prime[q] = {'absolute_mean': str(absolute), 'signed_mean': '0',
                       'conditional_mean_given_divisibility': str(delta(q, q))}
    observed = average([prod(abs(delta(n, q)) for q in primes) for n in values])
    predicted = prod(Fraction(2 * (q - 1), q**3) for q in primes)
    assert average([prod(1 + delta(n, q) for q in primes) for n in values]) == 1
    assert observed == predicted
    return {'primes': primes, 'period': period, 'local': by_prime,
            'mean_product_density': '1', 'mean_product_absolute_errors': str(observed),
            'all_divisible_product_absolute_errors': str(prod(delta(period, q) for q in primes))}


def main():
    result = {'scope': 'Artificial nonnegative local densities on one complete residue period, not Hermitian Gram fibers.',
              'cases': [check(primes) for primes in ((2,), (3,), (5,), (2, 3), (3, 5, 7), (2, 3, 5, 7, 11))]}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
