"""Independent integer controls; these do not construct an admissible Lean datum."""
from fractions import Fraction
from itertools import combinations
from math import comb, gcd, isqrt
import json

def prime(n):
    return n >= 2 and all(n % k for k in range(2, isqrt(n) + 1))

def check_parameters(q0, d):
    assert prime(d) and q0 % 18480 == 0
    assert (2 * (d + 1)) % q0 == 0 and (d + 1) % q0 != 0
    return dict(q0=q0, d=d, d_mod_16=d % 16, old_aux_q=11,
                minus_d_mod_11=(-d) % 11,
                legendre_minus_d_at_11=pow(-d, 5, 11))

def tower_degree(s):
    log3, t = 0, s
    while t >= 3:
        t //= 3
        log3 += 1
    return 3 ** (log3 + 5) * 2 ** s

def residue_control(q0, s):
    f = tower_degree(s)
    modulus = q0 * f
    plus = {1 + j * q0 for j in range(f) if gcd(1 + j * q0, modulus) == 1}
    minus = {(-1 + j * q0) % modulus for j in range(f) if gcd(-1 + j * q0, modulus) == 1}
    assert {(-x) % modulus for x in minus} == plus and len(plus) == f
    return dict(q0=q0, s=s, modulus=modulus, plus=len(plus), minus=len(minus))

def share_control():
    def discrepancy(T):
        even = sum(t % 2 == 0 for t in T)
        return abs(Fraction(even, len(T)) - Fraction(4, 7))
    hist = {}
    for T in combinations(range(16), 7):
        delta = str(discrepancy(T))
        hist[delta] = hist.get(delta, 0) + 1
    good = [0, 2, 4, 6, 1, 3, 5]
    bad = [0, 2, 4, 6, 8, 10, 12]
    assert hist['0'] == comb(8, 4) * comb(8, 3) == 3920
    assert sum(hist.values()) == comb(16, 7) == 11440
    assert discrepancy(good) == 0 and discrepancy(bad) == Fraction(3, 7)
    return dict(subset_size=7, modulus=16, exact_histogram=hist,
                exact_example=good, missed_coset_example=bad, missed_coset_discrepancy='3/7')

def main():
    params = [check_parameters(36960, 55439), check_parameters(18480, 9239)]
    assert params[1]['legendre_minus_d_at_11'] == 1
    print(json.dumps(dict(parameters=params,
        residue_controls=[residue_control(p['q0'], s) for p in params for s in range(4)],
        shares=share_control()), indent=2))

if __name__ == '__main__':
    main()
