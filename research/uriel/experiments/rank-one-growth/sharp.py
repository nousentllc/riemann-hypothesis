"""Certified infimum enclosure for the independently normalized six-square model."""
import argparse
import json
from fractions import Fraction
from math import isqrt
from pathlib import Path
from experiment import odd_factor


def primes_up_to(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = bytes(2)
    for k in range(2, isqrt(limit) + 1):
        if sieve[k]:
            sieve[k*k::k] = bytes(1 + (limit - k*k)//k)
    return [k for k in range(3, limit + 1) if sieve[k]]


def enclosure(limit, digits=18):
    scale = 10**digits
    lower = upper = 3 * scale // 4
    primes = primes_up_to(limit)
    for p in primes:
        if p % 4 == 1:
            num, den = p**3-1, p**3
        else:
            num, den = p**3+1, p*(p*p+1)
        lower = lower * num // den
        upper = (upper * num + den - 1) // den
    lower = lower * limit // (limit+1)
    return dict(limit=limit, odd_primes=len(primes), decimal_scale=scale,
                lower_numerator=lower, upper_numerator=upper)



def finite_search(limit):
    # Every odd integer has a unique smallest prime and coprime residual part.
    smallest = list(range(limit+1))
    for p in range(3, isqrt(limit)+1, 2):
        if smallest[p] == p:
            for m in range(p*p, limit+1, 2*p):
                if smallest[m] == m:
                    smallest[m] = p
    ratio = {1:Fraction(1)}
    records = [{'a':1,'relative_to_one':'1'}]
    best = Fraction(1)
    local = {}
    for a in range(3,limit+1,2):
        p = smallest[a]
        m, e = a, 0
        while m % p == 0:
            m //= p
            e += 1
        if (p,e) not in local:
            local[p,e] = odd_factor(p,e) / odd_factor(p,0)
        ratio[a] = ratio[m] * local[p,e]
        if ratio[a] < best:
            best = ratio[a]
            records.append({'a':a, 'relative_to_one':str(best)})
    # Independent divisor expansion with no factorization for the first 500 odd inputs.
    for a in range(1, min(limit,999)+1, 2):
        square = a*a
        divisors = {term for d in range(1,a+1) if square%d == 0 for term in (d,square//d)}
        reference = sum(Fraction(1 if d%4==1 else -1,d*d) for d in divisors)
        assert ratio[a] == reference
    answer = records[-1]['a']
    prime_factors = {}
    residual = answer
    while residual > 1:
        p = smallest[residual]
        prime_factors[p] = prime_factors.get(p,0)+1
        residual //= p
    # For the minimizing integer only: enclose U(a)/H, rounding each step up.
    scale = 10**18
    upper = scale
    cutoff = 100000
    for p in primes_up_to(cutoff):
        e = prime_factors.get(p,0)
        if p % 4 == 3:
            den = p**(4*e+2)
            upper = (upper*(den+1)+den-1)//den
        elif e:
            x = local[p,e]
            upper = (upper*x.numerator+x.denominator-1)//x.denominator
    assert answer <= cutoff
    upper = (upper*(cutoff+1)+cutoff-1)//cutoff
    return dict(limit=limit, odd_integers=len(ratio), strict_records=records,
                optimizer=answer, minimizers=[a for a,r in ratio.items() if r == best], independent_divisor_checks=500, factorization={str(k):v for k,v in prime_factors.items()},
                ratio_to_infimum_upper_numerator=upper, scale=scale)


def run():
    for p in primes_up_to(100):
        x = Fraction(1 if p % 4 == 1 else -1, p*p)
        for e in range(7):
            assert odd_factor(p,e) == odd_factor(p,0)*sum(x**k for k in range(2*e+1))
    boxes=[enclosure(n) for n in [100,1000,10000,100000,1000000]]
    for small,large in zip(boxes,boxes[1:]):
        assert small['lower_numerator'] <= large['lower_numerator'] < large['upper_numerator'] <= small['upper_numerator']
    return dict(intervals=boxes, finite_search=finite_search(100000), identity_cases=7*len(primes_up_to(100)),
                formula='(3/4) * prod_{p=1 mod 4}(1-p^-3) * prod_{p=3 mod 4}((1+p^-3)/(1+p^-2))')


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    result=run()
    path=Path(__file__).with_name('sharp.json')
    if parser.parse_args().write:
        path.write_text(json.dumps(result,indent=2)+'\n')
    else:
        assert json.loads(path.read_text())==result
    print(result['intervals'][-1])
