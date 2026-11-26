"""Exact finite checks of character orthogonality, ramp scaling, and quantifier controls."""
from collections import defaultdict
from fractions import Fraction as F
from math import gcd, isqrt, log, prod
import json


def primes(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((limit-p*p)//p+1)
    return [p for p in range(2, limit+1) if sieve[p]]


def local_character_sums(modulus, generators):
    # A generator of order m yields sum_j exp(2πije/m), equal to m iff e = 0.
    table = {1: 1}
    for g, order in generators:
        extended = {}
        for x, character_sum in table.items():
            for e in range(order):
                unit = x * pow(g, e, modulus) % modulus
                assert unit not in extended
                extended[unit] = character_sum * (order if e == 0 else 0)
        table = extended
    assert set(table) == {n for n in range(modulus) if gcd(n, modulus) == 1}
    return modulus, table


def experiment(q, d, y, factors):
    ps = primes(int(y))
    assert d in primes(d) and d % 2 and gcd(q,d) == 1
    phi = prod(len(t) for _, t in factors)
    direct, fourier, switched = (defaultdict(F) for _ in range(3))
    powers = 0
    for p in ps:
        n = p
        while n <= y:
            code = pow(n, (d-1)//2, d)
            assert code in {0, 1, d-1}
            twist = -1 if code == d-1 else code
            S = prod(t.get(n % m, 0) for m, t in factors)
            assert S == phi * int((n-1) % q == 0)
            new = max(F(1,n)-1/y, 0)
            old = max(y/n-1, 0)/y
            direct[p] += int((n-1)%q == 0)*(1-twist)*new
            fourier[p] += F(S,phi)*(1-twist)*old
            switched[p] += F(S,phi)*(1+twist)*old
            n *= p
            powers += 1
    assert direct == fourier and direct != switched
    nz = {str(k):str(v) for k,v in direct.items() if v}
    assert nz  # require a nonvacuous test at the main modulus
    return dict(q=q,d=d,y=str(y),phi=phi,prime_powers=powers,coefficients=nz,
                sign_swap_rejected=True)


def main():
    f4 = [local_character_sums(4, [(3,2)])]
    f18480 = [local_character_sums(16, [(15,2),(5,4)])] + [
        local_character_sums(p, [(g,p-1)]) for p,g in [(3,2),(5,2),(7,3),(11,2)]]
    d = next(p for p in primes(1000000) if p % 18480 == 9239)
    cases = [experiment(1,7,F(4),[]),experiment(4,7,F(43,2),f4),
             experiment(18480,d,F(800003,2),f18480)]
    assert cases[0]['coefficients'] == {'3':'1/6'}
    delta = sum(log(p)/(p-1) for p in (2,3,5,7,11))
    # A function zero on every window and one at a point in every gap (log coordinates).
    gaps = [(4**j, 3*4**j//2, 2*4**j, 4**(j+1)) for j in range(1,7)]
    assert all(a<b<c<e for a,b,c,e in gaps)
    assert 2*(64*3840+3)+26 == 491552
    print(json.dumps(dict(cases=cases, delta_main_approx=delta,
        normalized_delta_approx=delta/3840, real_coefficient=491552,
        gaps_in_log_coordinates=gaps, zero_order_examples=[[1,1,0],[1,0,1]]),indent=2))


if __name__ == '__main__':
    main()
